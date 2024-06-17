# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

import argparse
import json
import logging
import os
import sys


DESCRIPTION = """Print 2 tables in GitHub-flavored Markdown that summarize
an execution of CBMC proofs."""


def get_args():
    """Parse arguments for summarize script."""
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    for arg in [{
            "flags": ["--run-file"],
            "help": "path to the Litani run.json file",
            "required": True,
    }]:
        flags = arg.pop("flags")
        parser.add_argument(*flags, **arg)
    return parser.parse_args()


def _get_max_length_per_column_list(data):
    ret = [len(item) + 1 for item in data[0]]
    for row in data[1:]:
        for idx, item in enumerate(row):
            ret[idx] = max(ret[idx], len(item) + 1)
    return ret


def _get_table_header_separator(max_length_per_column_list):
    line_sep = ""
    for max_length_of_word_in_col in max_length_per_column_list:
        line_sep += "|" + "-" * (max_length_of_word_in_col + 1)
    line_sep += "|\n"
    return line_sep


def _get_entries(max_length_per_column_list, row_data):
    entries = []
    for row in row_data:
        entry = ""
        for idx, word in enumerate(row):
            max_length_of_word_in_col = max_length_per_column_list[idx]
            space_formatted_word = (max_length_of_word_in_col - len(word)) * " "
            entry += "| " + word + space_formatted_word
        entry += "|\n"
        entries.append(entry)
    return entries


def _get_rendered_table(data):
    table = []
    max_length_per_column_list = _get_max_length_per_column_list(data)
    entries = _get_entries(max_length_per_column_list, data)
    for idx, entry in enumerate(entries):
        if idx == 1:
            line_sep = _get_table_header_separator(max_length_per_column_list)
            table.append(line_sep)
        table.append(entry)
    table.append("\n")
    return "".join(table)


def _get_status_and_proof_summaries(run_dict):
    """Parse a dict representing a Litani run and create lists summarizing the
    proof results.

    Parameters
    ----------
    run_dict
        A dictionary representing a Litani run.


    Returns
    -------
    A list of 2 lists.
    The first sub-list maps a status to the number of proofs with that status.
    The second sub-list maps each proof to its status.
    """
    count_statuses = {}
    proofs = [["Proof", "Status"]]
    for proof_pipeline in run_dict["pipelines"]:
        status_pretty_name = proof_pipeline["status"].title().replace("_", " ")
        try:
            count_statuses[status_pretty_name] += 1
        except KeyError:
            count_statuses[status_pretty_name] = 1
        if proof_pipeline["name"] == "print_tool_versions":
            continue
        proofs.append([proof_pipeline["name"], status_pretty_name])
    statuses = [["Status", "Count"]]
    for status, count in count_statuses.items():
        statuses.append([status, str(count)])
    return [statuses, proofs]


def print_proof_results(out_file):
    """
    Print 2 strings that summarize the proof results.
    When printing, each string will render as a GitHub flavored Markdown table.
    """
    output = "## Summary of CBMC proof results\n\n"
    with open(out_file, encoding='utf-8') as run_json:
        run_dict = json.load(run_json)
    status_table, proof_table = _get_status_and_proof_summaries(run_dict)
    for summary in (status_table, proof_table):
        output += _get_rendered_table(summary)

    print(output)
    sys.stdout.flush()

    github_summary_file = os.getenv("GITHUB_STEP_SUMMARY")
    if github_summary_file:
        with open(github_summary_file, "a") as handle:
            print(output, file=handle)
            handle.flush()
    else:
        logging.warning(
            "$GITHUB_STEP_SUMMARY not set, not writing summary file")

    msg = (
        "Click the 'Summary' button to view a Markdown table "
        "summarizing all proof results")
    if run_dict["status"] != "success":
        logging.error("Not all proofs passed.")
        logging.error(msg)
        sys.exit(1)
    logging.info(msg)


if __name__ == '__main__':
    args = get_args()
    logging.basicConfig(format="%(levelname)s: %(message)s")
    try:
        print_proof_results(args.run_file)
    except Exception as ex: # pylint: disable=broad-except
        logging.critical("Could not print results. Exception: %s", str(ex))
