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

from versioning import update_version_number_in_freertos_component
from versioning import update_freertos_version_macros

from release import BaseRelease
from release import info
from release import indent_level
from release import logIndentPush
from release import logIndentPop

class UpdateSourceVersionKernel(BaseRelease):
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

    def updateVersionMacros(self, version_str):
        info('Updating version macros in task.h for "%s"' % version_str)

        # Extract major / minor / build from the version string.
        ver = re.search(r'([\d.]+)', version_str).group(1)
        (major, minor, build) = ver.split('.')
        update_freertos_version_macros(os.path.join(self.repo_path, 'include', 'task.h'), version_str, major, minor, build)

        self.commitChanges(self.commit_msg_prefix + 'Bump task.h version macros to "%s"' % version_str)

    def UpdateSourceVersionKernel(self):

        # Determine if we need to set a separate version macros for the main branch
        if (self.commit == 'HEAD') and len(self.main_br_version) > 0 and (self.main_br_version != self.version):
            # Update version macros for main branch
            self.updateVersionMacros(self.main_br_version)

            # Push the branch
            self.pushLocalCommits()

            # Revert the last commit in our working git repo
            self.local_repo.git.reset('--hard','HEAD^')

        # Update the version macros
        self.updateVersionMacros(self.version)

        if (self.commit == 'HEAD') and (self.main_br_version == self.version):
            # Share a task.h version number commit for main branch and release tag)
            self.pushLocalCommits()

        # When baselining off a non-HEAD commit, main is left unchanged by tagging a detached HEAD,
        # applying the autocommits, tagging, and pushing the new tag data to remote.
        # However in the detached HEAD state we don't have a branch to push to, so we skip

        # Update the header in each c/assembly file
        self.updateFileHeaderVersions(['FreeRTOS Kernel V','FreeRTOS Kernel <DEVELOPMENT BRANCH>'], 'FreeRTOS Kernel V%s' % self.version)

def configure_argparser():
    parser = ArgumentParser(description='FreeRTOS Release tool')

    parser.add_argument('git_org',
                        type=str,
                        metavar='GITHUB_ORG',
                        help='Git organization owner for FreeRTOS and FreeRTOS-Kernel. (i.e. "<git-org>/FreeRTOS.git")')

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

    # Update the source files
    if args.new_kernel_version:
        info('Starting to update source files...')
        logIndentPush()
        update_kernel_src_handler = UpdateSourceVersionKernel(mGit, args.new_kernel_version, args.kernel_commit, git_ssh=args.use_git_ssh,
                                   git_org=args.git_org, repo_path=args.kernel_repo_path, branch=args.kernel_repo_branch,
                                   main_br_version=args.new_kernel_main_br_version, do_not_push=args.do_not_push)
        update_kernel_src_handler.UpdateSourceVersionKernel()
        logIndentPop()

    info('Review script output for any unexpected behaviour.')
    info('Done.')

if __name__ == '__main__':
    main()
