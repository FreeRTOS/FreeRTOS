#!/usr/bin/env python3

import os, sys
from yaml import load
from yaml import CLoader as Loader

from git import Repo
from argparse import ArgumentParser

REPO_PATH=''

# List of submodules excluded from manifest.yml file
IGNORE_SUBMODULES_LIST = [ 
    'FreeRTOS-Plus/Test/CMock',
    'FreeRTOS/Test/CMock/CMock',
    'FreeRTOS/Test/litani'
    ]

# Obtain submodule path of all entries in manifest.yml file.
def read_manifest():
    path_list = []
    
    # Read YML file
    path_manifest = os.path.join(REPO_PATH, 'manifest.yml')
    assert os.path.exists(path_manifest), 'Missing manifest.yml'
    with open(path_manifest, 'r') as fp:
        manifest_data = fp.read()
    yml = load(manifest_data, Loader=Loader)
    assert 'dependencies' in yml, 'Manifest YML parsing error'

    # Iterate over all the "dependencies" entries, verify that
    # each contains entries for the following hierarchy:
    # name: "<library-name>"
    # version: "<version>"
    # repository:
    #   type: "git"
    #   url: <library-github-url>
    #   path: <path-to-submodule-in-repository>
    #
    for dep in yml['dependencies']:
        assert 'version' in dep, "Failed to parse 'version/tag' for submodule"
        assert 'repository' in dep and 'path' in dep['repository'] and 'url' in dep['repository'], "Failed to parse 'repository' object for submodule"
        path_list.append(dep['repository']['path'])

    return sorted(path_list)

# Generate list of submodules path in repository, excluding the
# path in IGNORES_SUBMODULES_LIST.
def get_all_submodules():
    path_list = []
    repo = Repo(REPO_PATH)
    for submodule in repo.submodules:
        path = submodule.abspath.replace(REPO_PATH+'/', '')
        if path not in IGNORE_SUBMODULES_LIST:
            path_list.append(path)
    
    return sorted(path_list)

if __name__ == '__main__':
    parser = ArgumentParser(description='manifest.yml verifier')
    parser.add_argument('--repo-root-path',
                        type=str,
                        required=None,
                        default=os.getcwd(),
                        help='Path to the repository root.')

    args = parser.parse_args()

    # Convert any relative path (like './') in passed argument to absolute path.
    REPO_PATH = os.path.abspath(args.repo_root_path)

    libraries_in_manifest_file = read_manifest()    
    git_submodules_list = get_all_submodules()

    print(REPO_PATH)
    print(git_submodules_list)

    # Check that manifest.yml contains entries for all submodules 
    # present in repository.
    if libraries_in_manifest_file == git_submodules_list:
        print('Manifest.yml is verified!')
        sys.exit(0)
    else:
        print('Manifest.yml is missing entries for:')
        # Find list of library submodules missing in manifest.yml
        for git_path in git_submodules_list:
            if git_path not in libraries_in_manifest_file:
                print(git_path)
        sys.exit(1)


