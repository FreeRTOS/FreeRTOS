#!/usr/bin/env python3
from __future__ import print_function
import sys
from enum import Enum


class Extractor(object):
    @staticmethod
    def __parse_ctags(tags_filename):
        def convert_excmd(excmd):
            assert excmd.endswith(';"')
            linenum = excmd[:-2]  # remove ';"'
            return int(linenum)
        result = {}
        with open(tags_filename) as f:
            for line in f:
                if line.startswith('!'):
                    continue
                parts = line.split('\t')
                funcname = parts[0]
                funcfile = parts[1]
                linenum = convert_excmd(parts[2])
                result[funcname] = (funcfile, linenum)
        return result

    def __init__(self, tags_filename):
        self.map = Extractor.__parse_ctags(tags_filename)

    class State(Enum):
        INIT = 0
        HEAD = 1
        BODY = 2

    def text_of_funcname(self, funcname):
        if funcname not in self.map:
            return []
        funcfile, linenum = self.map[funcname]
        result = []
        state, bracecount = Extractor.State.INIT, 0
        with open(funcfile) as f:
            for i, line in enumerate(f, start=1):  # ctags counts linenums from 1
                if state == Extractor.State.INIT and linenum <= i:
                    state = Extractor.State.HEAD
                if state == Extractor.State.HEAD:
                    result.append(line)
                    lbrace = line.count('{')
                    rbrace = line.count('}')
                    bracecount += lbrace
                    bracecount -= rbrace
                    if '{' in line:
                        state = Extractor.State.BODY
                        continue
                if state == Extractor.State.BODY:
                    result.append(line)
                    lbrace = line.count('{')
                    rbrace = line.count('}')
                    bracecount += lbrace
                    bracecount -= rbrace
                    if bracecount == 0:
                        break
        return result


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: %s <tagfile> <funcname>" % sys.argv[0])
        sys.exit(1)
    tag_filename = sys.argv[1]
    funcname = sys.argv[2]
    extractor = Extractor('tags')
    result = extractor.text_of_funcname(funcname)
    print(''.join(result))
    sys.exit(0)
