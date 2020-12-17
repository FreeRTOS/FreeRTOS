#!/usr/bin/env python3
import os, shutil
from yaml import load, dump
try:
    from yaml import CLoader as Loader, CDumper as Dumper
except ImportError:
    from yaml import Loader, Dumper
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
        self.repo_path = None
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

    def getRemoteEndpoint(self, repo_name):
        if self.git_ssh:
            return 'git@github.com:%s.git' % repo_name
        else:
            return 'https://github.com/%s.git' % repo_name

    def printReleases(self):
        releases = self.repo.get_releases()
        for r in releases:
            print(r)

    def pushAutoCommits(self):
        rc = push_git_tree_changes(self.repo_path, tag=self.tag, force_tag=True)
        assert rc == 0, 'Failed to upload git tree changes'

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

        # Download master:HEAD. Update its file header versions and kernel macros
        self.repo_path = download_git_tree(remote_name, '.', self.repo_path, 'master', 'HEAD')
        assert self.repo_path != None, 'Failed to download git tree'

    def updateFileHeaderVersions(self):
        '''
        Adds changes for two commits
            1.) Updates to file headers
            2.) Update to task.h macros
        Then tags commit #2 with the new tag version. Notes this will overwrite a tag it already exists
        Finally pushes all these changes
        '''
        target_version_prefixes = ['FreeRTOS Kernel V']
        update_version_number_in_freertos_component(self.repo_path, '.', target_version_prefixes, 'FreeRTOS Kernel V%s' % self.version)
        commit_git_tree_changes(self.repo_path, commit_message=self.commit_msg_prefix + 'Bump file header version to "%s"' % self.version)

    def updateVersionMacros(self):
        (major, minor, build) = self.version.split('.')
        update_freertos_version_macros(os.path.join(self.repo_path, 'include', 'task.h'), major, minor, build)
        commit_git_tree_changes(self.repo_path, commit_message=self.commit_msg_prefix + 'Bump task.h version macros to "%s"' % self.version)

    def createGitRelease(self):
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

        # Create the new release endpoint at upload assets
        release = self.repo.create_git_release(tag = self.tag,
                                               name = 'V%s' % (self.version),
                                               message = self.description,
                                               draft = False,
                                               prerelease = False)

class FreertosRelease(BaseRelease):
    def __init__(self, mGit, version, commit, git_ssh=False, git_org='FreeRTOS'):
        super().__init__(mGit, version, commit, git_ssh=git_ssh, git_org=git_org)

        self.repo_name = '%s/FreeRTOS' % self.git_org
        self.repo = mGit.get_repo(self.repo_name)
        self.tag = self.version
        self.description = 'Contains source code and example projects for the FreeRTOS Kernel and FreeRTOS+ libraries.'
        self.zip = None

        remote_name = self.getRemoteEndpoint(self.repo_name)
        self.repo_path = 'tmp-release-freertos'

        # Clean up any old work from previous runs
        if os.path.exists(self.repo_path):
            shutil.rmtree(self.repo_path)

        # Download master:HEAD. Update its file header versions and kernel submodule pointer
        self.repo_path = download_git_tree(remote_name, '.', self.repo_path, 'master', 'HEAD')
        assert self.repo_path != None, 'Failed to download git tree'

    def updateFileHeaderVersions(self):
        target_version_substrings = ['FreeRTOS Kernel V', 'FreeRTOS V']
        update_version_number_in_freertos_component(self.repo_path, '.', target_version_substrings, 'FreeRTOS V%s' % self.version)
        commit_git_tree_changes(self.repo_path, commit_message=self.commit_msg_prefix + 'Bump file header version to "%s"' % self.version)

    def updateSubmodulePointers(self):
        '''
        Reads the 'manifest.yml' file from the local FreeRTOS clone that is being used to stage the commits
        '''
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
            update_submodule_pointer(self.repo_path, submodule_path, submodule_tag)

        commit_git_tree_changes(self.repo_path, commit_message=self.commit_msg_prefix
                                                               + 'Bump submodules per manifest.yml for V%s' % self.version)

    def createReleaseZip(self):
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

    def createGitRelease(self):
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
    parser.add_argument('--new-core-version',
                        default=None,
                        required=False,
                        help='FreeRTOS-Kernel Version to replace old version. (Ex. "FreeRTOS Kernel V10.4.1")')

    parser.add_argument('--new-kernel-version',
                        default=None,
                        required=False,
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

def main():
    cmd = configure_argparser()
    args = cmd.parse_args()

    # Auth
    assert 'GITHUB_TOKEN' in os.environ, 'Set env{GITHUB_TOKEN} to an authorized git PAT'
    mGit = Github(os.environ.get('GITHUB_TOKEN'))

    # Create release or test
    if args.unit_test:
        return

    if args.new_kernel_version:
        rel_kernel = KernelRelease(mGit, args.new_kernel_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        rel_kernel.updateFileHeaderVersions()
        rel_kernel.updateVersionMacros()
        rel_kernel.pushAutoCommits()
        rel_kernel.createGitRelease()

    if args.new_core_version:
        rel_freertos = FreertosRelease(mGit, args.new_core_version, None, git_ssh=args.use_git_ssh, git_org=args.git_org)
        rel_freertos.updateFileHeaderVersions()
        rel_freertos.updateSubmodulePointers()
        rel_freertos.pushAutoCommits()
        rel_freertos.createReleaseZip()
        rel_freertos.createGitRelease()

    info('Review script output for any unexpected behaviour.')
    info('Release done.')

if __name__ == '__main__':
    main()
