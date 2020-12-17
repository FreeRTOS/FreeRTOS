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

from packager import prune_result_tree
from packager import RELATIVE_FILE_EXCLUDES as FREERTOS_RELATIVE_FILE_EXCLUDES

# PyGithub Git -  https://github.com/PyGithub/PyGithub
# PyGithub Docs - https://pygithub.readthedocs.io/en/latest/github_objects
# REST API used by PyGithub - https://developer.github.com/v3/

indent_level = 0

def logIndentPush():
    global indent_level
    indent_level += 4

def logIndentPop():
    global indent_level
    indent_level -= 4

    if indent_level < 0:
        indent_level = 0

def info(msg, end='\n'):
    print('[INFO]: %s%s' % (' ' * indent_level, str(msg)), end=end)

def warning(msg):
    print('[WARNING]: %s%s' % (' ' * indent_level, str(msg)))

def error(msg):
    print('[ERROR]: %s%s' % (' ' * indent_level, str(msg)))

def debug(msg):
    print('[DEBUG]: %s%s' % (' ' * indent_level, str(msg)))

# Callback for progress updates. For long spanning gitpython commands
def printDot(op_code, cur_count, max_count=None, message=''):
    if max_count == None or cur_count == max_count:
        print('.', end='')

class BaseRelease:
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS'):
        self.version = version
        self.tag_msg = 'Autocreated by FreeRTOS Git Tools.'
        self.commit = commit
        self.git_ssh = git_ssh
        self.git_org = git_org
        self.repo_path = None
        self.local_repo = None
        self.commit_msg_prefix = '[AUTO][RELEASE]: '
        self.description = ''

        self.mGit = mGit # Save a handle to the authed git session

    def updateFileHeaderVersions(self):
        '''
        Updates for all FreeRTOS/FreeRTOS files, not including submodules, to have their file header
        versions updated to match this release version. It creates the release tag and stores these updates there,
        at a detached commit (akin to a branch).
        '''
        assert False, 'Implement me'

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
        push_infos = self.local_repo.remote('origin').push(force=force)

        # Check for any errors
        for info in push_infos:
            assert 0 == info.flags & PushInfo.ERROR, 'Failed to push changes to ' + str(info)

    def pushTag(self):
        # Overwrite existing tags
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

    def deleteGitRelease(self):
        info('Deleting git release endpoint for "%s"' % self.tag)

        try:
            self.repo.get_release(self.tag).delete_release()
        except UnknownObjectException:
            info('A release endpoint does not exist for "%s". No need to erase.' % self.tag)
        except:
            assert False, 'Encountered error while trying to delete git release endpoint'

    def rollbackAutoCommits(self, n_autocommits=2):
        info('Rolling back "%s" autocommits' % self.tag)

        if self.tag not in self.local_repo.tags:
            error('Could not find a SHA to rollback to for tag "%s"' % self.tag)
            return False

        # Search for auto release SHAs that match the release tag SHA
        tag_commit = self.local_repo.tag('refs/tags/%s' % self.tag).commit
        prior_commit = self.local_repo.commit(tag_commit.hexsha + '~%d' % n_autocommits)
        n_commits_searched = 0
        for commit in self.local_repo.iter_commits():
            if n_commits_searched > 25:
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
        info('Restoring "master" to just before autorelease:%s' % self.version)

        self.deleteGitRelease()
        self.rollbackAutoCommits()
        self.deleteTag()
        self.pushLocalCommits(force=True)


class KernelRelease(BaseRelease):
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS'):
        super().__init__(mGit, version, commit, git_ssh=git_ssh, git_org=git_org)

        self.repo_name = '%s/FreeRTOS-Kernel' % self.git_org
        self.repo = mGit.get_repo(self.repo_name)
        self.tag = 'V%s' % version

        # Download a local git repo for pushing commits
        remote_name = self.getRemoteEndpoint(self.repo_name)
        self.repo_path = 'tmp-release-freertos-kernel'

        # Clean up any old work from previous runs
        if os.path.exists(self.repo_path):
            shutil.rmtree(self.repo_path)

        # Clone the target repo for creating the release autocommits
        info('Downloading a local repo to make commits...', end='')
        self.local_repo = Repo.clone_from(remote_name, self.repo_path, progress=printDot)
        print()

    def updateFileHeaderVersions(self):
        '''
        Adds changes for two commits
            1.) Updates to file headers
            2.) Update to task.h macros
        Then tags commit #2 with the new tag version. Notes this will overwrite a tag it already exists
        Finally pushes all these changes
        '''
        info('Updating file header versions for "%s"' % self.version)

        target_version_prefixes = ['FreeRTOS Kernel V']
        update_version_number_in_freertos_component(self.repo_path, '.', target_version_prefixes, 'FreeRTOS Kernel V%s' % self.version)

        self.commitChanges(self.commit_msg_prefix + 'Bump file header version to "%s"' % self.version)

    def updateVersionMacros(self):
        info('Updating version macros in task.h for "%s"' % self.version)

        (major, minor, build) = self.version.split('.')
        update_freertos_version_macros(os.path.join(self.repo_path, 'include', 'task.h'), major, minor, build)

        self.commitChanges(self.commit_msg_prefix + 'Bump task.h version macros to "%s"' % self.version)

    def createGitRelease(self):
        '''
        Creates/Overwrites release identified by target tag
        '''
        info('Creating git release endpoint for "%s"' % self.tag)

        # If this release already exists, delete it
        try:
            release_queried = self.repo.get_release(self.tag)

            info('Overwriting existing git release endpoint for "%s"...' % self.tag)
            release_queried.delete_release()
        except UnknownObjectException:
            info('Creating git release endpoint for "%s"...' % self.tag)

        # Create the new release endpoint at upload assets
        release = self.repo.create_git_release(tag = self.tag,
                                               name = 'V%s' % (self.version),
                                               message = self.description,
                                               draft = False,
                                               prerelease = False)

    def autoRelease(self):
        info('Creating kernel "FreeRTOS Kernel V%s"' % self.version)

        self.updateFileHeaderVersions()
        self.updateVersionMacros()
        self.pushLocalCommits()
        self.pushTag()
        self.createGitRelease()


class FreertosRelease(BaseRelease):
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS'):
        super().__init__(mGit, version, commit, git_ssh=git_ssh, git_org=git_org)

        self.repo_name = '%s/FreeRTOS' % self.git_org
        self.repo = mGit.get_repo(self.repo_name)
        self.tag = self.version
        self.description = 'Contains source code and example projects for the FreeRTOS Kernel and FreeRTOS+ libraries.'
        self.zip_path = 'FreeRTOSv%s.zip' % self.version

        remote_name = self.getRemoteEndpoint(self.repo_name)
        self.repo_path = 'tmp-release-freertos'

        # Clean up any old work from previous runs
        if os.path.exists(self.repo_path):
            shutil.rmtree(self.repo_path)

        # Clone the target repo for creating the release autocommits
        info('Downloading a local repo to make commits...', end='')
        self.local_repo = Repo.clone_from(remote_name, self.repo_path, progress=printDot)
        print()

    def isValidManifestYML(self, path_yml):
        assert False, 'Unimplemented'

    def updateFileHeaderVersions(self):
        info('Updating file header versions to "%s"' % self.version)

        target_version_substrings = ['FreeRTOS Kernel V', 'FreeRTOS V']
        update_version_number_in_freertos_component(self.repo_path, '.', target_version_substrings, 'FreeRTOS V%s' % self.version)

        self.commitChanges(self.commit_msg_prefix + 'Bump file header version to "%s"' % self.version)

    def updateSubmodulePointers(self):
        '''
        Reads the 'manifest.yml' file from the local FreeRTOS clone that is being used to stage the commits
        '''
        info('Updating submodules to match manifest.yml')

        path_manifest = os.path.join(self.repo_path, 'manifest.yml')
        assert os.path.exists(path_manifest), 'Missing manifest.yml'

        with open(path_manifest, 'r') as fp:
            manifest_data = fp.read()

        yml = load(manifest_data, Loader=Loader)
        assert 'dependencies' in yml, 'Manifest YML parsing error'
        for dep in yml['dependencies']:
            assert 'version' in dep, 'Failed to parse submodule tag from manifest'
            assert 'repository' in dep and 'path' in dep['repository'], 'Failed to parse submodule path from manifest'
            submodule_path = dep['repository']['path']
            submodule_tag  = dep['version']

            # Update the submodule to point to version noted in manifest file
            self.updateSubmodulePointer(submodule_path, submodule_tag)

        self.commitChanges(self.commit_msg_prefix + 'Bump submodules per manifest.yml for V%s' % self.version)

    def createReleaseZip(self):
        '''
        At the moment, the only asset we upload is the
        '''
        zip_name = 'FreeRTOSv%s' % self.version
        info('Packaging "%s"' % zip_name)

        # This path name is retained in zip, so we don't name it 'tmp-*' but rather keep it consistent with previous
        # packaging
        zip_root_path = zip_name
        rel_repo_path = os.path.join(zip_root_path, zip_name)

        # Clean up any old work from previous runs
        if os.path.exists(zip_root_path):
            shutil.rmtree(zip_root_path)

        # To keep consistent with previous packages
        os.mkdir(zip_root_path)

        # Download a fresh copy for packaging
        info('Downloading fresh copy of %s for packing...' % zip_name, end='')
        packaged_repo = Repo.clone_from(self.getRemoteEndpoint(self.repo_name),
                                        rel_repo_path,
                                        multi_options=['-b%s' % self.tag, '--recurse-submodules'],
                                        progress=printDot)
        print()

        # Prune then zip package
        info('Pruning from release zip...')
        pruned_files = prune_result_tree(rel_repo_path, FREERTOS_RELATIVE_FILE_EXCLUDES)

        info('Compressing "%s"...' % self.zip_path)
        with zipfile.ZipFile(self.zip_path, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zip:
            for root, dirs, files in os.walk(zip_root_path):
                for file in files:
                    # For some strange reason, we have broken symlinks...avoid these
                    file_path = os.path.join(root, file)
                    if os.path.islink(file_path) and not os.path.exists(file_path):
                        warning('Skipping over broken symlink "%s"' % file_path)
                    else:
                        zip.write(file_path)



    def createGitRelease(self):
        '''
        Creates/Overwrites release identified by target tag
        '''
        info('Creating git release endpoint for "%s"' % self.tag)

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

        release.upload_asset(self.zip_path, name='FreeRTOSv%s.zip' % self.version, content_type='application/zip')

    def autoRelease(self):
        info('Creating core release "FreeRTOS V%s"' % self.version)

        self.updateFileHeaderVersions()
        self.updateSubmodulePointers()
        self.pushLocalCommits()
        self.pushTag()
        self.createReleaseZip()
        self.createGitRelease()

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

    parser.add_argument('--rollback-core-version',
                        default=None,
                        required=False,
                        help='Reset "master" to state prior to autorelease of given core version')

    parser.add_argument('--new-kernel-version',
                        default=None,
                        required=False,
                        help='Reset "master" to just before the autorelease for the specified kernel version")')

    parser.add_argument('--rollback-kernel-version',
                        default=None,
                        required=False,
                        help='Reset "master" to state prior to autorelease of the given kernel version')

    parser.add_argument('--use-git-ssh',
                        default=True,
                        action='store_false',
                        help='Use SSH endpoints to interface git remotes, instead of HTTPS')

    parser.add_argument('--unit-test',
                        action='store_true',
                        default=False,
                        help='Run unit tests.')

    return parser

def main():
    cmd = configure_argparser()
    args = cmd.parse_args()

    # Auth
    assert 'GITHUB_TOKEN' in os.environ, 'Set env{GITHUB_TOKEN} to an authorized git PAT'
    mGit = Github(os.environ.get('GITHUB_TOKEN'))

    # Unit tests
    if args.unit_test:
        rel_freertos = FreertosRelease(mGit, args.new_core_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)

        # Undo a release
        rel_freertos.deleteGitRelease()
        rel_freertos.rollbackAutoCommits()
        rel_freertos.deleteTag()
        rel_freertos.pushLocalCommits(force=True)
        return

    # Create Releases
    if args.new_kernel_version:
        info('Starting kernel release...')
        logIndentPush()
        rel_kernel = KernelRelease(mGit, args.new_kernel_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        rel_kernel.autoRelease()
        logIndentPop()

    if args.new_core_version:
        info('Starting core release...')
        logIndentPush()
        rel_freertos = FreertosRelease(mGit, args.new_core_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        rel_freertos.autoRelease()
        logIndentPop()

    # Undo autoreleases
    if args.rollback_kernel_version:
        info('Starting kernel rollback...')
        rel_kernel = KernelRelease(mGit, args.rollback_kernel_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        logIndentPush()
        rel_kernel.restorePriorToRelease()
        logIndentPop()

    if args.rollback_core_version:
        info('Starting core rollback...')
        logIndentPush()
        rel_freertos = FreertosRelease(mGit, args.rollback_core_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        rel_freertos.restorePriorToRelease()
        logIndentPop()

    info('Review script output for any unexpected behaviour.')
    info('Release done.')

if __name__ == '__main__':
    main()
