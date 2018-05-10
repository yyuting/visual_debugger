import programslice
import programslice.visitor
import programslice.formatter
import ast
import astmonkey
from astmonkey import transformers
import re
import dependency_util

def build_graph(node):
    
    visitor = programslice.visitor.LineDependencyVisitor()
    visitor.visit(node)
    
    return visitor.graph

def add_annotation(node_list):
    
    for i in range(len(node_list)):
        parent = node_list[i].parent
        
        for field, value in ast.iter_fields(parent):
            if isinstance(value, list):
                try:
                    index = value.index(node_list[i])
                    value[index:index] = ast.parse('"""transforms(parallel())"""').body
                except:
                    continue
    return

def test():
    
    path = '../../apps/blur_two_stage/blur_two_stage.py'
    s_orig = open(path, 'rt').read()
    
    head = re.compile(r'#!\/.*\n|#.*coding[:=]\s*(?P<enc>[-\w.]+).*')
    source = head.sub('', s_orig)
    node = ast.parse(source)
    node = transformers.ParentNodeTransformer().visit(node)
    
    graph = build_graph(node)
    
    varname = 'a'
    line = 5
    col = 4
    
    start = programslice.graph.Edge(varname, line, col)
    result = programslice.graph.Slice(graph)(start)
    
    print(s_orig)
    
    print('--------------------------------')
    
    print('variables dependent on a at position (5, 4):')
    print()
    
    test_result = programslice.formatter.VimOutPutFormatter(result, path)()
    
    for i in range(1, len(test_result)):
        print(test_result[i])
    
    find_for_node = dependency_util.FindForNode()
    find_for_node.visit(node)
    
    print('--------------------------------')
    print('original defnode:')
    print(node.body[1].body)
    print('--------------------------------')
    add_annotation(find_for_node.fornode)
    print('defnode after adding annotation:')
    print(node.body[1].body)
    
    return

if __name__ == "__main__":
    
    test()
    
    