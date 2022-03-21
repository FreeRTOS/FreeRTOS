#!/usr/bin/env python3

import os, sys
from argparse import ArgumentParser
import shutil
from zipfile import ZipFile
import subprocess

FREERTOS_GIT_LINK = 'https://github.com/FreeRTOS/FreeRTOS.git'
LABS_GIT_LINK = 'https://github.com/FreeRTOS/FreeRTOS-Labs.git'

DIR_INTERMEDIATE_FILES = os.path.join(os.path.basename(__file__).replace('.py', '-tmp-output'))
DIR_INPUT_TREES = os.path.join(DIR_INTERMEDIATE_FILES, 'baseline')
DIR_OUTPUT_TREES = os.path.join(DIR_INTERMEDIATE_FILES, 'git-head-master')

RELATIVE_FILE_EXCLUDES = [
    os.path.join('.git'),
    os.path.join('.github'),
    os.path.join('.gitignore'),
    os.path.join('.gitmodules'),
    os.path.join('CONTRIBUTING.md'),
    os.path.join('LICENSE.md'),
    os.path.join('README.md'),

    os.path.join('FreeRTOS', 'Source', '.git'),
    os.path.join('FreeRTOS', 'Source', '.github'),
    os.path.join('FreeRTOS', 'Source', 'CONTRIBUTING.md'),
    os.path.join('FreeRTOS', 'Source', 'GitHub-FreeRTOS-Kernel-Home.url'),
    os.path.join('FreeRTOS', 'Source', 'History.txt'),
    os.path.join('FreeRTOS', 'Source', 'LICENSE.md'),
    os.path.join('FreeRTOS', 'Source', 'Quick_Start_Guide.url'),
    os.path.join('FreeRTOS', 'Source', 'README.md'),
    os.path.join('FreeRTOS', 'Source', 'SECURITY.md'),
]

LABS_RELATIVE_EXCLUDE_FILES = [
    os.path.join('.git')
]

# -------------------------------------------------------------------------------------------------
# Helpers
# -------------------------------------------------------------------------------------------------
def info(msg):
    print('[INFO]: %s' % str(msg))

def authorize_filetree_diff():
    '''
    Presents the filetree diff between baseline zip and resulting zip contents.
    Then queries a 'y/n' response from user, to verify file diff.
    This does not consider files that were pruned from result filetree and is to instead show

    Return boolean True if user authorizes the diff, else False
    '''
    info('TODO')

def get_file_bytesize_diff(path_newfile, path_basefile):
    return os.path.getsize(path_newfile) - os.path.getsize(path_basefile)

# -------------------------------------------------------------------------------------------------
# Core
# -------------------------------------------------------------------------------------------------
def cleanup_intermediate_files(scratch_dir):
    '''
    Undo and cleanup actions done by 'setup_intermediate_files()'
    '''
    if os.path.exists(scratch_dir):
        shutil.rmtree(scratch_dir)

def unzip_baseline_zip(path_inzip, path_outdir):
    '''
    Unzips baseline zip into intermediate files directory. The baseline zip is used to compare against
    resulting output zip and its contents, to produce filetree diffs, size diffs, or other diagnostics
    '''
    with ZipFile(path_inzip, 'r') as inzip:
        inzip.extractall(path_outdir)

    return os.path.join(path_outdir, str(os.path.basename(path_inzip)).replace('.zip', ''))

def download_git_tree(git_link, root_dir, dir_name, ref='master', commit_id='HEAD', recurse=False):
    '''
    Download HEAD from Git Master. Place into working files dir
    '''
    args = ['git', '-C', root_dir, 'clone', '-b', ref, git_link, dir_name]
    subprocess.run(args, check=True)
    subprocess.run(['git', '-C', os.path.join(root_dir, dir_name), 'checkout', '-f', commit_id], check=True)
    subprocess.run(['git', '-C', os.path.join(root_dir, dir_name), 'clean', '-fd'], check=True)
    if recurse:
        subprocess.run(['git', '-C', os.path.join(root_dir, dir_name), 'submodule', 'update', '--init', '--recursive'], check=True)

    return os.path.join(root_dir, dir_name)

def commit_git_tree_changes(repo_dir, commit_message=''):
    subprocess.run(['git', '-C', repo_dir, 'add', '-u'], check=True)
    subprocess.run(['git', '-C', repo_dir, 'commit', '-m', commit_message], check=True)

    return 0

def push_git_tree_changes(repo_dir, tag=None, force_tag=False):
    subprocess.run(['git', '-C', repo_dir, 'push'], check=True)

    if tag != None:
        force_tag_arg = '-f' if force_tag else ''
        subprocess.run(['git', '-C', repo_dir, 'tag', force_tag_arg, tag], check=True)
        subprocess.run(['git', '-C', repo_dir, 'push', force_tag_arg, '--tags'], check=True)

    return 0

def update_submodule_pointer(repo_dir, rel_submodule_path, new_submodule_ref):
    subprocess.run(['git', '-C', repo_dir, 'submodule', 'update', '--init'], check=True)
    subprocess.run(['git', '-C', os.path.join(repo_dir, rel_submodule_path), 'fetch'], check=True)
    subprocess.run(['git', '-C', os.path.join(repo_dir, rel_submodule_path), 'checkout', new_submodule_ref], check=True)
    subprocess.run(['git', '-C', repo_dir, 'add', rel_submodule_path], check=True)

    return 0

def setup_intermediate_files(scratch_dir, intree_dir, outtree_dir):
    cleanup_intermediate_files(scratch_dir)
    os.mkdir(scratch_dir)
    os.mkdir(intree_dir)
    os.mkdir(outtree_dir)

def create_file_trees(intree_dir, baseline_zip, outtree_dir, git_link, outtree_name, git_ref='master', commit_id='HEAD'):
    path_in_tree = None
    path_out_tree = None

    # Input baseline file tree
    if baseline_zip != None:
        print("Unzipping baseline: '%s'..." % baseline_zip)
        path_in_tree = unzip_baseline_zip(baseline_zip, intree_dir)
        print('Done.')

    # Output file tree to be pruned and packaged
    path_out_tree = download_git_tree(git_link, outtree_dir, outtree_name, commit_id=commit_id)

    return (path_in_tree, path_out_tree)

def prune_result_tree(path_root, exclude_files=[], dry_run=False):
    '''
    Remove all files specifed in 'exclude_files' from intermediate result file tree.
    Paths in 'exclude_files' are taken relative to path_root
    '''
    files_removed = []
    for f in exclude_files:
        path_full = os.path.join(path_root, f)
        if os.path.exists(path_full):
            if os.path.isfile(path_full):
                if not dry_run:
                    os.remove(path_full)
                files_removed.append(path_full)
            else:
                if not dry_run:
                    shutil.rmtree(path_full)
                files_removed.append(path_full)

    return files_removed

def prune_result_tree_v2(tree_root, exclude_files=[], dry_run=False):
    '''
    Remove all files in 'exclude_files' from file tree.
    '''
    files_removed = []
    for root, dirs, files in os.walk(tree_root):
        for dir in dirs:
            if dir in exclude_files:
                path_full = os.path.join(root, dir)
                if not dry_run:
                    shutil.rmtree(path_full)
                files_removed.append(path_full)
        for file in files:
            if file in exclude_files:
                path_full = os.path.join(root, file)
                if not dry_run:
                    os.remove(path_full)
                files_removed.append(path_full)
    return files_removed

def zip_result_tree(path_tree, path_outzip):
    '''
    Zip file tree rooted at 'path_root', using same compression as 7z at max compression,
    to zip at 'path_outzip'
    '''
    subprocess.run(['7z', 'a', '-tzip', '-mx=9', path_outzip, os.path.join('.', path_tree, '*')])

def show_package_diagnostics(path_newzip, path_basezip):
    '''
    Show various diagnostics about resulting package zip including Byte-size diff from baseline
    and a path to
    '''
    if path_basezip:
        size_diff_KB = get_file_bytesize_diff(path_newzip, path_basezip) / 1024
        print('\nPackage growth from baseline:\n    size(%s) - size(%s) = %s%.2d KB' %
              (path_newzip,
               path_basezip,
               '+' if size_diff_KB >= 0 else '', size_diff_KB))

def create_package(path_ziproot, path_outtree, package_name, exclude_files=[]):
    print("Packaging '%s'..." % package_name)
    pruned_files = prune_result_tree(path_outtree, exclude_files)
    print('Files removed:\n    %s' % '\n    '.join(pruned_files))

    path_outzip = '%s.zip' % package_name
    zip_result_tree(path_ziproot, path_outzip)
    print('Done.')

    return path_outzip

# -------------------------------------------------------------------------------------------------
# CLI
# -------------------------------------------------------------------------------------------------
def configure_argparser():
    parser = ArgumentParser(description = 'Zip packaging tool for FreeRTOS release.')

    parser.add_argument('--core-input-zip',
                        metavar = 'CORE-BASELINE.ZIP',
                        default = None,
                        help = 'FreeRTOS baseline zip to compare against new core zip')

    parser.add_argument('--labs-input-zip',
                        metavar = 'LABS-BASELINE.ZIP',
                        default = None,
                        help = 'FreeRTOS-Labs baseline zip to compare agains new labs zip')

    parser.add_argument('--zip-version',
                        metavar = 'PACKAGE_VERSION_NUMBER',
                        type = str,
                        default = None,
                        help = 'Version number to be suffixed to FreeRTOS and FreeRTOS-Labs zips')

    parser.add_argument('--freertos-commit',
                        metavar = 'FREERTOS_COMMIT_ID',
                        type = str,
                        default = 'HEAD',
                        help = 'Commit ID of FreeRTOS repo to package')

    return parser

def sanitize_cmd_args(args):
    # Check FreeRTOS Core options
    if not args.core_input_zip:
        info('No FreeRTOS baseline zip provided. Zip-comparison diagnostics will not be provided...')
        args.core_input_zip = None
    elif not os.path.exists(args.core_input_zip):
        error('Input zip does not exist: %s' % args.core_input_zip)
        exit(1)

    # Check FreeRTOS Labs options
    if not args.labs_input_zip:
        info('No FreeRTOS-Labs baseline zip provided. Zip-comparison diagnostics will not be provided...')
        args.labs_input_zip = None
    elif not os.path.exists(args.labs_input_zip):
        error('Input zip does not exist: %s' % args.input_zip)
        exit(1)

    # Check version options
    if args.zip_version == None:
        info('No version string provide. Will use "XX.YY.ZZ" as version suffix...')
        args.zip_version = 'XX.YY.ZZ'


def main():
    # CLI
    cmd = configure_argparser()

    # Setup
    args = cmd.parse_args()
    sanitize_cmd_args(args)
    setup_intermediate_files(DIR_INTERMEDIATE_FILES, DIR_INPUT_TREES, DIR_OUTPUT_TREES)

    # Create FreeRTOS and FreeRTOS-Labs packages
    core_package_name = 'FreeRTOSv%s' % args.zip_version
    (path_core_in_tree, path_core_out_tree) = create_file_trees(DIR_INPUT_TREES,
                                                                args.core_input_zip,
                                                                DIR_OUTPUT_TREES,
                                                                FREERTOS_GIT_LINK,
                                                                core_package_name,
                                                                commit_id=args.freertos_commit)

    if path_core_out_tree == None:
        print('Failed to prepare repo for zipping')
        exit(1);

    core_outzip = create_package(path_core_out_tree, core_package_name, RELATIVE_FILE_EXCLUDES)

    # Create FreeRTOS-Labs package
    labs_package_name = 'FreeRTOS-Labs'
    (path_labs_in_tree, path_labs_out_tree) = create_file_trees(DIR_INPUT_TREES,
                                                                args.labs_input_zip,
                                                                DIR_OUTPUT_TREES,
                                                                LABS_GIT_LINK,
                                                                labs_package_name)
    if path_labs_out_tree == None:
        print('Failed to prepare repo for zipping')
        exit(1);

    labs_outzip = create_package(path_labs_out_tree, labs_package_name, LABS_RELATIVE_EXCLUDE_FILES)

    # Package summaries
    show_package_diagnostics(core_outzip, args.core_input_zip)
    show_package_diagnostics(labs_outzip, args.labs_input_zip)

if __name__ == '__main__':
    main()

