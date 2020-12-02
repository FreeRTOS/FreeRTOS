#!/usr/bin/env python3
import os, shutil
from argparse import ArgumentParser

import re
import datetime
from github import Github
from github.GithubException import *
from github.InputGitAuthor import InputGitAuthor

from versioning import update_version_number_in_freertos_component
from versioning import update_freertos_version_macros

from packager import download_git_tree
from packager import update_submodule_pointer
from packager import commit_git_tree_changes
from packager import push_git_tree_changes
from packager import create_package
from packager import RELATIVE_FILE_EXCLUDES as FREERTOS_RELATIVE_FILE_EXCLUDES

# PyGithub Git -  https://github.com/PyGithub/PyGithub
# PyGithub Docs - https://pygithub.readthedocs.io/en/latest/github_objects
# REST API used by PyGithub - https://developer.github.com/v3/

'''
FUTURE ENHANCEMENTS
    - Add mechanism that restores state of all affected to repos to BEFORE this script was run
    - Input sanitizing
        - Include regex patterns that MUST be honored for version strings, etc.
    - Create a companion dependencies file that can be piped to pip3
    - Ease of HTTPS authentication
        - This should make it very easy to port to Github action. Currently, Github action mostly operates with 
          via https endpoints, rather than SSH
    - Break down some functions and any repeated work --> more granular (reasonably), less duplicated code
    - Unit tests
        - Theres already an option and some desired tests laid out via comments. See bottom
    - All of the scratch-work directories/files should be placed under a single directory the name of which makes obvious
      that it's a scratch-work dir (Ex. tmp-*, scratch-*, etc.)
    - Intermediate checks
        - 
'''

def info(msg, indent_level=0):
    print('%s[INFO]: %s' % (' ' * indent_level, str(msg)))

def warning(msg, indent_level=0):
    print('%s[WARNING]: %s' % (' ' * indent_level, str(msg)))

def error(msg, indent_level=0):
    print('%s[ERROR]: %s' % (' ' * indent_level, str(msg)))

def debug(msg, indent_level=0):
    print('%s[DEBUG]: %s' % (' ' * indent_level, str(msg)))

class BaseRelease:
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS'):
        self.version = version
        self.tag_msg = 'Autocreated by FreeRTOS Git Tools.'
        self.commit = commit
        self.git_ssh = git_ssh
        self.git_org = git_org
        self.commit_msg_prefix = '[AUTO][RELEASE]: '

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

    def getRemoteEndpoint(self, repo_name):
        if self.git_ssh:
            return 'git@github.com:%s.git' % repo_name
        else:
            return 'https://github.com/%s.git' % repo_name

    def printReleases(self):
        releases = self.repo.get_releases()
        for r in releases:
            print(r)

class KernelRelease(BaseRelease):
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS'):
        super().__init__(mGit, version, commit, git_ssh=git_ssh, git_org=git_org)

        self.repo_name = '%s/FreeRTOS-Kernel' % self.git_org
        self.repo = mGit.get_repo(self.repo_name)
        self.tag = 'V%s' % version

    def updateFileHeaderVersions(self, old_version_prefix):
        '''
        Adds changes for two commits
            1.) Updates to file headers
            2.) Update to task.h macros
        Then tags commit #2 with the new tag version. Notes this will overwrite a tag it already exists
        Finally pushes all these changes
        '''
        remote_name = self.getRemoteEndpoint(self.repo_name)
        rel_repo_path = 'tmp-versioning-freertos-kernel'

        # Clean up any old work from previous runs
        if os.path.exists(rel_repo_path):
            shutil.rmtree(rel_repo_path)

        # Download master:HEAD. Update its file header versions and kernel macros
        repo_path = download_git_tree(remote_name, '.', rel_repo_path, 'master', 'HEAD')
        assert repo_path != None, 'Failed to download git tree'

        update_version_number_in_freertos_component(repo_path, '.', old_version_prefix, 'FreeRTOS Kernel V%s' % self.version)
        commit_git_tree_changes(rel_repo_path, commit_message=self.commit_msg_prefix + 'Bump file header version to "%s"' % self.version)

        (major, minor, build) = self.version.split('.')
        update_freertos_version_macros(os.path.join(repo_path, 'include', 'task.h'), major, minor, build)
        commit_git_tree_changes(rel_repo_path, commit_message=self.commit_msg_prefix + 'Bump task.h version macros to "%s"' % self.version)

        # Commit the versioning, tag it, and upload all to remote
        rc = push_git_tree_changes(repo_path, tag=self.tag, force_tag=True)
        assert rc == 0, 'Failed to upload git tree changes'


class FreertosRelease(BaseRelease):
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS'):
        super().__init__(mGit, version, commit, git_ssh=git_ssh, git_org=git_org)

        self.repo_name = '%s/FreeRTOS' % self.git_org
        self.repo = mGit.get_repo(self.repo_name)
        self.tag = self.version
        self.description = 'Contains source code and example projects for the FreeRTOS Kernel and FreeRTOS+ libraries.'
        self.zip = None

    def updateFileHeaderVersions(self, old_version_prefix, new_kernel_ref):
        remote_name = self.getRemoteEndpoint(self.repo_name)
        rel_repo_path = 'tmp-versioning-freertos'

        # Clean up any old work from previous runs
        if os.path.exists(rel_repo_path):
            shutil.rmtree(rel_repo_path)

        # Download master:HEAD. Update its file header versions and kernel submodule pointer
        repo_path = download_git_tree(remote_name, '.', rel_repo_path, 'master', 'HEAD')
        assert repo_path != None, 'Failed to download git tree'

        update_version_number_in_freertos_component(repo_path, '.', old_version_prefix, 'FreeRTOS V%s' % self.version)
        commit_git_tree_changes(repo_path, commit_message=self.commit_msg_prefix + 'Bump file header version to "%s"' % self.version)

        update_submodule_pointer(repo_path, os.path.join('FreeRTOS', 'Source'), new_kernel_ref)
        commit_git_tree_changes(repo_path, commit_message=self.commit_msg_prefix + 'Bump kernel pointer "%s"' % new_kernel_ref)

        # Commit the versioning, tag it, and upload all to remote
        rc = push_git_tree_changes(repo_path, tag=self.tag, force_tag=True)
        assert rc == 0, 'Failed to upload git tree changes'

    def CreateReleaseZip(self):
        '''
        At the moment, the only asset we upload is the
        '''
        remote_name = self.getRemoteEndpoint(self.repo_name)

        # This path name is retained in zip, so we don't name it 'tmp-*' but rather keep it consistent with previous
        # packaging
        repo_name = 'FreeRTOSv%s' % self.version
        zip_root_path = repo_name
        rel_repo_path = os.path.join(zip_root_path, repo_name)

        # Clean up any old work from previous runs
        if os.path.exists(zip_root_path):
            shutil.rmtree(zip_root_path)

        # To keep consistent with previous packages
        os.mkdir(zip_root_path)

        # Download master:HEAD. Update its file header versions and kernel submodule pointer
        repo_path = download_git_tree(remote_name, '.', rel_repo_path, 'master', self.tag, recurse=True)
        assert repo_path != None, 'Failed to download git tree'

        self.zip = create_package(zip_root_path,
                                  rel_repo_path,
                                  'FreeRTOSv%s' % self.version,
                                  exclude_files=FREERTOS_RELATIVE_FILE_EXCLUDES)

    def Upload(self):
        '''
        Creates/Overwrites release identified by target tag
        '''

        # If this release already exists, delete it
        try:
            release_queried = self.repo.get_release(self.tag)

            info('Deleting existing release "%s"...' % self.tag)
            release_queried.delete_release()
        except UnknownObjectException:
            info('Creating release/tag "%s"...' % self.tag)

        # Create the new release endpoind at upload assets
        release = self.repo.create_git_release(tag = self.tag,
                                               name = 'FreeRTOSv%s' % (self.version),
                                               message = self.description,
                                               draft = False,
                                               prerelease = False)

        release.upload_asset(self.zip, name='FreeRTOSv%s.zip' % self.version, content_type='application/zip')


def configure_argparser():
    parser = ArgumentParser(description='FreeRTOS Release tool')

    parser.add_argument('--old-core-version',
                        default=None,
                        required=True,
                        help='FreeRTOS Version to match and replace. (Ex. FreeRTOS V202011.00)')

    parser.add_argument('--new-core-version',
                        default=None,
                        required=True,
                        help='FreeRTOS Version to replace old version. (Ex. FreeRTOS V202011.00)')

    parser.add_argument('--old-kernel-version',
                        default=None,
                        required=True,
                        help='FreeRTOS-Kernel Version to match and replace. (Ex. "FreeRTOS Kernel V10.4.1")')

    parser.add_argument('--new-kernel-version',
                        default=None,
                        required=True,
                        help='FreeRTOS-Kernel Version to replace old version. (Ex. "FreeRTOS Kernel V10.4.1")')

    parser.add_argument('--git-org',
                        default='FreeRTOS',
                        required=False,
                        help='Git organization owner for FreeRTOS and FreeRTOS-Kernel. (i.e. "<git-org>/FreeRTOS.git")')

    parser.add_argument('--use-git-ssh',
                        default=False,
                        action='store_true',
                        help='Use SSH endpoints to interface git remotes, instead of HTTPS')


    parser.add_argument('--unit-test',
                        action='store_true',
                        default=False,
                        help='Run unit tests.')

    return parser

def sanitize_cmd_args(args):
    info('TODO: Add cmdline input sanitizing')

def main():
    # CLI
    cmd = configure_argparser()

    # Setup
    args = cmd.parse_args()
    sanitize_cmd_args(args)

    # Auth
    assert 'GITHUB_TOKEN' in os.environ, 'You must set env variable GITHUB_TOKEN to an authorized git PAT'
    mGit = Github(os.environ.get('GITHUB_TOKEN'))

    if args.unit_test:
        pass
    else:
        # Update versions
        rel_kernel = KernelRelease(mGit, args.new_kernel_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        rel_kernel.updateFileHeaderVersions(args.old_kernel_version)

        rel_freertos = FreertosRelease(mGit, args.new_core_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        rel_freertos.updateFileHeaderVersions(args.old_core_version, 'V%s' % args.new_kernel_version)

        # Package contents of FreeRTOS/FreeRTOS and upload release assets to Git
        rel_freertos.CreateReleaseZip()
        rel_freertos.Upload()

    info('Review script output for any unexpected behaviour.')
    info('Release done.')

if __name__ == '__main__':
    main()

#--------------------------------------------------------------------
#                              TESTING
#--------------------------------------------------------------------
# Create new tag, verify creation

# Create release endpoint, delete it, verify deletion

# Overwrite an existing tag

# Perform full operation, restore to state before operation, verify restored state

# Run zipping operation, check versions, pathing, etc
