#!/usr/bin/env python3

from __future__ import print_function
from pycparser import c_parser, c_ast, parse_file
import sys

ignore_callee = set(['mutex_acquire', 'mutex_release'])
ignore_caller = set(['caller_reinstates_queue_predicate'])
proven = [
    'prvCopyDataFromQueue',
    'prvCopyDataToQueue',
    'prvInitialiseNewQueue',
    'prvIsQueueEmpty',
    'prvIsQueueFull',
    'prvLockQueue',
    'prvUnlockQueue',
    'uxQueueMessagesWaiting',
    'uxQueueSpacesAvailable',
    'vQueueDelete',
    'xQueueGenericCreate',
    'xQueueGenericReset',
    'xQueueGenericSend',
    'xQueueGenericSendFromISR',
    'xQueueIsQueueEmptyFromISR',
    'xQueueIsQueueFullFromISR',
    'xQueuePeek',
    'xQueuePeekFromISR',
    'xQueueReceive',
    'xQueueReceiveFromISR',
]

modeled = [
    'setInterruptMask',
    'clearInterruptMask',
    'setInterruptMaskFromISR',
    'clearInterruptMaskFromISR',
    'vTaskSuspendAll',
    'xTaskResumeAll',
]

CALLMAP = set()


class FuncCallVisitor(c_ast.NodeVisitor):
    def __init__(self, caller):
        self.caller = caller

    def visit_FuncCall(self, node):
        callee = node.name.name
        if callee not in ignore_callee:
            CALLMAP.add((node.name.name, self.caller))


class FuncDefVisitor(c_ast.NodeVisitor):
    def visit_FuncDef(self, node):
        caller = node.decl.name
        if caller in ignore_caller:
            return
        if caller.startswith('wrapper_'):
            caller = caller[8:]
        v = FuncCallVisitor(caller)
        v.visit(node)


def show_func_calls(filename):
    ast = parse_file(filename, use_cpp=False)
    v = FuncDefVisitor()
    v.visit(ast)


if __name__ == "__main__":
    filename = 'out.pp'
    show_func_calls(filename)
    print('digraph G {')
    print('  rankdir=LR;')
    print('  node [style = filled, colorscheme = set13;];')
    for f in proven:
        print('  %s [fillcolor = 3];' % f)
    for f in modeled:
        print('  %s [fillcolor = 2];' % f)
    for (callee, caller) in CALLMAP:
        print('  %s -> %s;' % (callee, caller))
    print('}')
