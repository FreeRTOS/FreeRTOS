#!/usr/bin/env python3
import os, shutil
from yaml import load, dump
try:
    from yaml import CLoader as Loader, CDumper as Dumper
except ImportError:
    from yaml import Loader, Dumper
from argparse import ArgumentParser

# For interfacing Git REST API
import re
import datetime
from github import Github
from github.GithubException import *
from github.InputGitAuthor import InputGitAuthor

# Local interfacing of repo
from git import Repo
from git import PushInfo

import zipfile

from versioning import update_version_number_in_freertos_component
from versioning import update_freertos_version_macros

from packager import prune_result_tree, prune_result_tree_v2
from packager import RELATIVE_FILE_EXCLUDES as FREERTOS_RELATIVE_FILE_EXCLUDES

# PyGithub Git -  https://github.com/PyGithub/PyGithub
# PyGithub Docs - https://pygithub.readthedocs.io/en/latest/github_objects
# REST API used by PyGithub - https://developer.github.com/v3/

indent_level = 0

# Files/Directories not to be included in the FreeRTOS-Kernel release.
KERNEL_RELEASE_EXCLUDE_FILES = [
    '.git',
    '.github',
    '.gitignore',
    '.gitmodules'
]

def logIndentPush():
    global indent_level
    indent_level += 4

def logIndentPop():
    global indent_level
    indent_level -= 4

    if indent_level < 0:
        indent_level = 0

def info(msg, end='\n'):
    print('[INFO]: %s%s' % (' ' * indent_level, str(msg)), end=end, flush=True)

def warning(msg):
    print('[WARNING]: %s%s' % (' ' * indent_level, str(msg)), flush=True)

def error(msg):
    print('[ERROR]: %s%s' % (' ' * indent_level, str(msg)), flush=True)

def debug(msg):
    print('[DEBUG]: %s%s' % (' ' * indent_level, str(msg)), flush=True)

# Callback for progress updates. For long spanning gitpython commands
def printDot(op_code, cur_count, max_count=None, message=''):
    if max_count == None or cur_count == max_count:
        print('.', end='')

class BaseRelease:
    def __init__(self, mGit, version, commit='HEAD', git_ssh=False, git_org='FreeRTOS', repo_path=None, branch='main', do_not_push=False):
        self.version = version
        self.tag_msg = 'Autocreated by FreeRTOS Git Tools.'
        self.commit = commit
        self.git_ssh = git_ssh
        self.git_org = git_org
        self.repo_path = repo_path
        self.local_repo = None
        self.branch = branch
        self.commit_msg_prefix = '[AUTO][RELEASE]: '
        self.description = ''
        self.mGit = mGit # Save a handle to the authed git session
        self.do_not_push = do_not_push

        if self.repo_path:
            info('Sourcing "%s" to make local commits' % self.repo_path)
            self.local_repo = Repo(self.repo_path)

    def CheckRelease(self):
        '''
        Sanity checks for the release. Verify version number format. Check zip size.
        Ensure version numbers were updated, etc.
        '''
        assert False, 'Add release check'

    def hasTag(self, tag):
        remote_tags = self.repo.get_tags()
        for t in remote_tags:
            if t.name == tag:
                return True

        return False

    def commitChanges(self, msg):
        assert self.local_repo != None, 'Failed to commit. Git repo uninitialized.'

        info('Committing: "%s"' % msg)
        self.local_repo.git.add(update=True)
        commit = self.local_repo.index.commit(msg)

    def getRemoteEndpoint(self, repo_name):
        if self.git_ssh:
            return 'git@github.com:%s.git' % repo_name
        else:
            return 'https://github.com/%s.git' % repo_name

    def printReleases(self):
        releases = self.repo.get_releases()
        for r in releases:
            print(r)

    def pushLocalCommits(self, force=False):
        if self.do_not_push:
            info('Skipping to push local commits...')
        else:
            info('Pushing local commits...')
            push_infos = self.local_repo.remote('origin').push(force=force)

            # Check for any errors
            for push_info in push_infos:
                assert 0 == push_info.flags & PushInfo.ERROR, 'Failed to push changes to ' + str(push_info)

    def pushTag(self):
        if self.do_not_push:
            info('Skipping to push tag "%s"' % self.tag)
        else:
            # Overwrite existing tags
            info('Pushing tag "%s"' % self.tag)
            tag_info = self.local_repo.create_tag(self.tag, message=self.tag_msg, force=True)
            self.local_repo.git.push(tags=True, force=True)

    def deleteTag(self):
        # Remove from remote
        if self.tag in self.local_repo.tags:
            info('Deleting tag "%s"' % self.tag)
            self.local_repo.remote('origin').push(':%s' % self.tag)
        else:
            info('A tag does not exists for "%s". No need to delete.' % self.tag)

    def updateSubmodulePointer(self, rel_path, ref):
        submodule = Repo(rel_path)
        submodule.remote('origin').fetch()
        submodule.git.checkout(ref)

    def updateFileHeaderVersions(self, old_version_substrings, new_version_string):
        info('Updating file header versions for "%s"...' % self.version, end='')
        n_updated = 0
        n_updated += update_version_number_in_freertos_component(self.repo_path,
                                                                 '.',
                                                                 old_version_substrings,
                                                                 new_version_string,
                                                                 exclude_hidden=True)

        n_updated += update_version_number_in_freertos_component(os.path.join('.github', 'scripts'),
                                                                 self.repo_path,
                                                                 old_version_substrings,
                                                                 new_version_string,
                                                                 exclude_hidden=False)

        print('...%d Files updated.' % n_updated)

        self.commitChanges(self.commit_msg_prefix + 'Bump file header version to "%s"' % self.version)

    def deleteGitRelease(self):
        info('Deleting git release endpoint for "%s"' % self.tag)

        try:
            self.repo.get_release(self.tag).delete_release()
        except UnknownObjectException:
            info('A release endpoint does not exist for "%s". No need to erase.' % self.tag)
        except:
            assert False, 'Encountered error while trying to delete git release endpoint'

    def rollbackAutoCommits(self, n_autocommits=2, n_search=25):
        info('Rolling back "%s" autocommits' % self.tag)

        if self.tag not in self.local_repo.tags:
            error('Could not find a SHA to rollback to for tag "%s"' % self.tag)
            return False

        # Search for auto release SHAs that match the release tag SHA
        tag_commit = self.local_repo.tag('refs/tags/%s' % self.tag).commit
        prior_commit = self.local_repo.commit(tag_commit.hexsha + '~%d' % n_autocommits)
        n_commits_searched = 0
        for commit in self.local_repo.iter_commits():
            if n_commits_searched > n_search:
                error('Exhaustively searched but could not find tag commit to rollback')
                return False

            if (self.commit_msg_prefix in commit.message
                    and commit.hexsha == tag_commit.hexsha
                    and self.version in commit.message):

                info('Found matching tag commit %s. Reverting to prior commit %s'
                        % (tag_commit.hexsha, prior_commit.hexsha))

                # Found the commit prior to this autorelease. Revert back to it then push
                self.local_repo.git.reset(prior_commit.hexsha, hard=True)
                self.pushLocalCommits(force=True)
                return True

            n_commits_searched += 1

        return False

    def restorePriorToRelease(self):
        info('Restoring "main" to just before autorelease:%s' % self.version)

        self.deleteGitRelease()
        self.rollbackAutoCommits()
        self.deleteTag()
        self.pushLocalCommits(force=True)


class KernelRelease(BaseRelease):
    def __init__(self, mGit, version, commit='HEAD', git_ssh=False, git_org='FreeRTOS', repo_path=None, branch='main', main_br_version='', do_not_push=False):
        super().__init__(mGit, version, commit=commit, git_ssh=git_ssh, git_org=git_org, repo_path=repo_path, branch=branch, do_not_push=do_not_push)

        self.repo_name = '%s/FreeRTOS-Kernel' % self.git_org
        self.repo = mGit.get_repo(self.repo_name)
        self.tag = 'V%s' % version
        self.description = 'Contains source code for the FreeRTOS Kernel.'
        self.zip_path = 'FreeRTOS-KernelV%s.zip' % self.version
        self.main_br_version = main_br_version

        # Parent ctor configures local_repo if caller chooses to source local repo from repo_path.
        if self.repo_path is None:
            self.repo_path = 'tmp-release-freertos-kernel'
            if os.path.exists(self.repo_path):
                shutil.rmtree(self.repo_path)

            # Clone the target repo for creating the release autocommits
            remote_name = self.getRemoteEndpoint(self.repo_name)
            info('Downloading %s@%s to baseline auto-commits...' % (remote_name, commit), end='')
            self.local_repo = Repo.clone_from(remote_name, self.repo_path, progress=printDot, branch=self.branch)

        # In case user gave non-HEAD commit to baseline
        self.local_repo.git.checkout(commit)

        print()



    def createReleaseZip(self):
        '''
        At the moment, the only asset we upload is the source code.
        '''
        zip_name = 'FreeRTOS-KernelV%s' % self.version
        info('Packaging "%s"' % zip_name)
        logIndentPush()

        # This path name is retained in zip, so we don't name it 'tmp-*' but
        # rather keep it consistent.
        rel_repo_path = zip_name

        # Clean up any old work from previous runs.
        if os.path.exists(rel_repo_path):
            shutil.rmtree(rel_repo_path)

        # Download a fresh copy for packaging.
        info('Downloading fresh copy of %s for packing...' % zip_name, end='')
        packaged_repo = Repo.clone_from(self.getRemoteEndpoint(self.repo_name),
                                        rel_repo_path,
                                        multi_options=['--depth=1', '-b%s' % self.tag, '--recurse-submodules'],
                                        progress=printDot,
                                        branch=self.branch)
        print()

        # Prune then zip package.
        info('Pruning from release zip...', end='')
        files_pruned = prune_result_tree_v2(rel_repo_path, KERNEL_RELEASE_EXCLUDE_FILES)
        print('...%d Files Removed.' % len(files_pruned))

        info('Compressing "%s"...' % self.zip_path)
        with zipfile.ZipFile(self.zip_path, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zip:
            for root, dirs, files in os.walk(rel_repo_path):
                for file in files:
                    # For some strange reason, we have broken symlinks...avoid these.
                    file_path = os.path.join(root, file)
                    if os.path.islink(file_path) and not os.path.exists(file_path):
                        warning('Skipping over broken symlink "%s"' % file_path)
                    else:
                        zip.write(file_path)

        logIndentPop()

    def createGitRelease(self):
        '''
        Creates/Overwrites release identified by target tag
        '''
        if self.do_not_push:
            info('Skipping creating git release endpoint for "%s"...' % self.tag)
        else:
            # If this release already exists, delete it
            try:
                release_queried = self.repo.get_release(self.tag)

                info('Overwriting existing git release endpoint for "%s"...' % self.tag)
                release_queried.delete_release()
            except UnknownObjectException:
                info('Creating git release endpoint for "%s"...' % self.tag)

            # Create the release asset to upload.
            self.createReleaseZip()

            # Create the new release endpoint at upload assets
            release = self.repo.create_git_release(tag = self.tag,
                                                name = 'V%s' % (self.version),
                                                message = self.description,
                                                draft = False,
                                                prerelease = False)
            info('Uploading release asssets...')
            release.upload_asset(self.zip_path, name='FreeRTOS-KernelV%s.zip' % self.version, content_type='application/zip')

    def autoRelease(self):
        info('Auto-releasing FreeRTOS Kernel V%s' % self.version)

        self.pushTag()

        self.createGitRelease()

        info('Kernel release done.')



class FreertosRelease(BaseRelease):
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS', repo_path=None, branch='main', do_not_push=False):
        super().__init__(mGit, version, commit, git_ssh=git_ssh, git_org=git_org, repo_path=repo_path, branch=branch, do_not_push=do_not_push)

        self.repo_name = '%s/FreeRTOS' % self.git_org
        self.repo = mGit.get_repo(self.repo_name)
        self.tag = self.version
        self.description = 'Contains source code and example projects for the FreeRTOS Kernel and FreeRTOS+ libraries.'
        self.zip_path = 'FreeRTOSv%s.zip' % self.version

        # Download a fresh copy of local repo for making autocommits, if necessary
        if self.repo_path is None:
            self.repo_path = 'tmp-release-freertos'

            # Clean up any old work from previous runs
            if os.path.exists(self.repo_path):
                shutil.rmtree(self.repo_path)

            # Clone the target repo for creating the release autocommits
            remote_name = self.getRemoteEndpoint(self.repo_name)
            info('Downloading %s@%s to baseline auto-commits...' % (remote_name, commit), end='')
            self.local_repo = Repo.clone_from(remote_name, self.repo_path, progress=printDot, branch=self.branch)

        # In support of non-HEAD baselines
        self.local_repo.git.checkout(commit)
        print()

    def isValidManifestYML(self, path_yml):
        assert False, 'Unimplemented'

    def updateSubmodulePointers(self):
        '''
        Reads the 'manifest.yml' file from the local FreeRTOS clone that is being used to stage the commits
        '''

        info('Initializing first level of submodules...')
        self.local_repo.submodule_update(init=True, recursive=False)

        # Read YML file
        path_manifest = os.path.join(self.repo_path, 'manifest.yml')
        assert os.path.exists(path_manifest), 'Missing manifest.yml'
        with open(path_manifest, 'r') as fp:
            manifest_data = fp.read()
        yml = load(manifest_data, Loader=Loader)
        assert 'dependencies' in yml, 'Manifest YML parsing error'

        # Update all the submodules per yml
        logIndentPush()
        for dep in yml['dependencies']:
            assert 'version' in dep, 'Failed to parse submodule tag from manifest'
            assert 'repository' in dep and 'path' in dep['repository'], 'Failed to parse submodule path from manifest'
            submodule_path = dep['repository']['path']
            submodule_tag  = dep['version']

            # Update the submodule to point to version noted in manifest file
            info('%-20s : %s' % (dep['name'], submodule_tag))
            self.updateSubmodulePointer(os.path.join(self.repo_path, submodule_path), submodule_tag)
        logIndentPop()

        self.commitChanges(self.commit_msg_prefix + 'Bump submodules per manifest.yml for V%s' % self.version)

    def createReleaseZip(self):
        '''
        At the moment, the only asset we upload is the
        '''
        zip_name = 'FreeRTOSv%s' % self.version
        info('Packaging "%s"' % zip_name)
        logIndentPush()

        # This path name is retained in zip, so we don't name it 'tmp-*' but rather keep it consistent with previous
        # packaging
        rel_repo_path = zip_name

        # Clean up any old work from previous runs
        if os.path.exists(rel_repo_path):
            shutil.rmtree(rel_repo_path)

        # Download a fresh copy for packaging
        info('Downloading fresh copy of %s for packing...' % zip_name, end='')
        packaged_repo = Repo.clone_from(self.getRemoteEndpoint(self.repo_name),
                                        rel_repo_path,
                                        multi_options=['--depth=1', '-b%s' % self.tag, '--recurse-submodules'],
                                        progress=printDot,
                                        branch=self.branch)
        print()

        # Prune then zip package
        info('Pruning from release zip...', end='')
        files_pruned = prune_result_tree(rel_repo_path, FREERTOS_RELATIVE_FILE_EXCLUDES)
        print('...%d Files Removed.' % len(files_pruned))

        info('Compressing "%s"...' % self.zip_path)
        with zipfile.ZipFile(self.zip_path, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zip:
            for root, dirs, files in os.walk(rel_repo_path):
                for file in files:
                    # For some strange reason, we have broken symlinks...avoid these
                    file_path = os.path.join(root, file)
                    if os.path.islink(file_path) and not os.path.exists(file_path):
                        warning('Skipping over broken symlink "%s"' % file_path)
                    else:
                        zip.write(file_path)

        logIndentPop()

    def createGitRelease(self):
        '''
        Creates/Overwrites release identified by target tag
        '''
        if self.do_not_push:
            info('Skipping creating git release endpoint for "%s"...' % self.tag)
        else:
            # If this release already exists, delete it
            try:
                release_queried = self.repo.get_release(self.tag)

                info('Overwriting existing git release endpoint for "%s"...' % self.tag)
                release_queried.delete_release()
            except UnknownObjectException:
                info('Creating git release endpoint for "%s"...' % self.tag)

            # Create the new release endpoind at upload assets
            release = self.repo.create_git_release(tag = self.tag,
                                                name = 'FreeRTOSv%s' % (self.version),
                                                message = self.description,
                                                draft = False,
                                                prerelease = False)

            info('Uploading release asssets...')
            release.upload_asset(self.zip_path, name='FreeRTOSv%s.zip' % self.version, content_type='application/zip')

    def autoRelease(self):
        info('Auto-releasing FreeRTOS V%s' % self.version)

        self.updateFileHeaderVersions(['FreeRTOS Kernel V', 'FreeRTOS V', 'FreeRTOS Kernel <DEVELOPMENT BRANCH>', 'FreeRTOS <DEVELOPMENT BRANCH>'], 'FreeRTOS V%s' % self.version)
        self.updateSubmodulePointers()
        # When baselining off a non-HEAD commit, main is left unchanged by tagging a detached HEAD,
        # applying the autocommits, tagging, and pushing the new tag data to remote.
        # However in the detached HEAD state we don't have a branch to push to, so we skip
        if self.commit == 'HEAD':
            self.pushLocalCommits()

        self.pushTag()
        self.createReleaseZip()
        self.createGitRelease()

        info('Core release done.')

def configure_argparser():
    parser = ArgumentParser(description='FreeRTOS Release tool')

    parser.add_argument('git_org',
                        type=str,
                        metavar='GITHUB_ORG',
                        help='Git organization owner for FreeRTOS and FreeRTOS-Kernel. (i.e. "<git-org>/FreeRTOS.git")')

    parser.add_argument('--new-core-version',
                        default=None,
                        required=False,
                        help='FreeRTOS Standard Distribution Version to replace old version. (Ex. "FreeRTOS V202012.00")')

    parser.add_argument('--core-commit',
                        default='HEAD',
                        required=False,
                        metavar='GITHUB_SHA',
                        help='Github SHA to baseline autorelease')

    parser.add_argument('--rollback-core-version',
                        default=None,
                        required=False,
                        help='Reset "main" to state prior to autorelease of given core version')

    parser.add_argument('--core-repo-path',
                        type=str,
                        default=None,
                        required=False,
                        help='Instead of downloading from git, use existing local repos for autocommits')

    parser.add_argument('--core-repo-branch',
                        type=str,
                        default='main',
                        required=False,
                        help='Branch of FreeRTOS hub repository to release.')

    parser.add_argument('--new-kernel-version',
                        default=None,
                        required=False,
                        help='Reset "main" to just before the autorelease for the specified kernel version")')

    parser.add_argument('--new-kernel-main-br-version',
                        default='',
                        required=False,
                        help='Set the version in task.h on the kernel main branch to the specified value.')

    parser.add_argument('--kernel-commit',
                        default='HEAD',
                        required=False,
                        metavar='GITHUB_SHA',
                        help='Github SHA to baseline autorelease')

    parser.add_argument('--rollback-kernel-version',
                        default=None,
                        required=False,
                        help='Reset "main" to state prior to autorelease of the given kernel version')

    parser.add_argument('--kernel-repo-path',
                        type=str,
                        default=None,
                        required=False,
                        help='Instead of downloading from git, use existing local repos for autocommits')

    parser.add_argument('--kernel-repo-branch',
                        type=str,
                        default='main',
                        required=False,
                        help='Branch of FreeRTOS Kernel repository to release.')

    parser.add_argument('--use-git-ssh',
                        default=False,
                        action='store_true',
                        help='Use SSH endpoints to interface git remotes, instead of HTTPS')

    parser.add_argument('--unit-test',
                        action='store_true',
                        default=False,
                        help='Run unit tests.')

    parser.add_argument('--do-not-push',
                        action='store_true',
                        default=False,
                        help='Do not push the changes but only make local commits.')

    return parser

def main():
    cmd = configure_argparser()
    args = cmd.parse_args()

    # Auth
    if not args.do_not_push:
        assert 'GITHUB_TOKEN' in os.environ, 'Set env{GITHUB_TOKEN} to an authorized git PAT'
    mGit = Github(os.environ.get('GITHUB_TOKEN'))

    # Unit tests
    if args.unit_test:
        return

    # Create Releases
    if args.new_kernel_version:
        info('Starting kernel release...')
        logIndentPush()
        rel_kernel = KernelRelease(mGit, args.new_kernel_version, args.kernel_commit, git_ssh=args.use_git_ssh,
                                   git_org=args.git_org, repo_path=args.kernel_repo_path, branch=args.kernel_repo_branch,
                                   main_br_version=args.new_kernel_main_br_version, do_not_push=args.do_not_push)
        rel_kernel.autoRelease()
        logIndentPop()

    if args.new_core_version:
        info('Starting core release...')
        logIndentPush()
        rel_freertos = FreertosRelease(mGit, args.new_core_version, args.core_commit, git_ssh=args.use_git_ssh,
                                       git_org=args.git_org, repo_path=args.core_repo_path, branch=args.core_repo_branch,
                                       do_not_push=args.do_not_push)
        rel_freertos.autoRelease()
        logIndentPop()

    # Undo autoreleases
    if args.rollback_kernel_version:
        info('Starting kernel rollback...')
        rel_kernel = KernelRelease(mGit, args.rollback_kernel_version, args.kernel_commit, git_ssh=args.use_git_ssh,
                                   git_org=args.git_org, repo_path=args.kernel_repo_path, branch=args.kernel_repo_branch,
                                   do_not_push=args.do_not_push)
        logIndentPush()
        rel_kernel.restorePriorToRelease()
        logIndentPop()

    if args.rollback_core_version:
        info('Starting core rollback...')
        logIndentPush()
        rel_freertos = FreertosRelease(mGit, args.rollback_core_version, args.core_commit, git_ssh=args.use_git_ssh,
                                       git_org=args.git_org, repo_path=args.core_repo_path, branch=args.core_repo_branch,
                                       do_not_push=args.do_not_push)
        rel_freertos.restorePriorToRelease()
        logIndentPop()

    info('Review script output for any unexpected behaviour.')
    info('Done.')

if __name__ == '__main__':
    main()
