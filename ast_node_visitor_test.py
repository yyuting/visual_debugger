import ast_node_visitor
import ast
import sys
from astmonkey import transformers
from sympy.parsing.sympy_parser import parse_expr
import astunparse
import visualize

def find_direction(write, reads):
    """
    given the write of an assignment node and reads of assignment node, (all of them are arrays with same dimension), find the index direction
    currently using sympy to parse the expression, might need to implement my own
    """
    write_depth = len(write.parent.slice.value.elts)
    write_index = []
    for i in range(write_depth):
        write_index.append(astunparse.unparse(write.parent.slice.value.elts[i]).replace('\n', ''))

    direction = {}
    for i in range(len(reads)):
        if len(reads[i].parent.slice.value.elts) == write_depth:
            try:
                direction_i = []
                for j in range(write_depth):
                    read_index = astunparse.unparse(reads[i].parent.slice.value.elts[j]).replace('\n', '')
                    direction_str = read_index + '-' + write_index[j]
                    direction_eval = parse_expr(direction_str)
                    direction_int = int(direction_eval)
                    direction_i.append(direction_int)
                direction.setdefault(i, direction_i)
            except:
                pass
            
    return direction

def find_direction_in_iteration_index(write, reads, index):
    """
    given the write of an assignment node and reads of assignment node, (all of them are arrays with same dimension), find the index direction
    currently using sympy to parse the expression, might need to implement my own
    """
    write_depth = len(write.parent.slice.value.elts)
    write_index = []
    for i in range(write_depth):
        write_index.append(astunparse.unparse(write.parent.slice.value.elts[i]).replace('\n', ''))

    direction = {}
    for i in range(len(reads)):
        if len(reads[i].parent.slice.value.elts) == write_depth:
            try:
                direction_i = []
                for j in range(write_depth):
                    read_index = astunparse.unparse(reads[i].parent.slice.value.elts[j]).replace('\n', '')
                    direction_str = read_index + '-' + write_index[j]
                    direction_eval = parse_expr(direction_str)
                    direction_int = int(direction_eval)
                    direction_i.append(direction_int)
                direction.setdefault(i, direction_i)
            except:
                pass
            
    return direction
    
if __name__ == "__main__":
    
    if len(sys.argv) < 2:
        path = 'dependency_test.py'
    else:
        path = sys.argv[1]
        method_name = sys.argv[2]
    
    source = open(path, 'rt').read()
    node = ast.parse(source)
    node = transformers.ParentNodeTransformer().visit(node)
    visitor = ast_node_visitor.DependencyVisitor()
    visitor.visit(node)
    
    for return_node in visitor.def_info[method_name]['return']:
        for write_node in visitor.def_info[method_name]['write'][return_node.id]:
            if isinstance(write_node.parent, ast.Subscript):
                read_nodes = [tnode for tnode in visitor.def_info[method_name]['write_to_read'][write_node] if tnode.id in visitor.array_name]
                direction = find_direction(write_node, read_nodes)
    
    """write = node.body[2].body[3].body[0].body[0].targets[0].value
    reads = []
    reads.append(node.body[2].body[3].body[0].body[0].value.left.right.value)
    reads.append(node.body[2].body[3].body[0].body[0].value.left.left.right.value)
    reads.append(node.body[2].body[3].body[0].body[0].value.left.left.left.value)
    
    direction = find_direction(write, reads)
    
    print(direction)"""
    
    write = node.body[2].body[4].body[0].body[0].targets[0].value
    reads = []
    reads.append(node.body[2].body[4].body[0].body[0].value.left.right.value)
    reads.append(node.body[2].body[4].body[0].body[0].value.left.left.right.value)
    reads.append(node.body[2].body[4].body[0].body[0].value.left.left.left.value)
    
    direction = find_direction(write, reads)

    visualize.animate_input_output(direction=direction, title='output_img <- temp_img')
    
    """try:
        defnode = visitor.def_info[method_name]['node']
        return_value = visitor.def_info[method_name]['return']
        return_names = []
        for i in range(len(return_value)):
            try:
                return_name = return_value[i].id
                if return_name not in return_names:
                    return_names.append(return_name)
            except:
                pass
        
        #only process the situtaion when there's only one variable to be returned
        if len(return_names == 1):
            return_id = return_names[0]
            if return_id in visitor.def_info[method_name]['array']:
                write_return = [tnode for tnode in visitor.def_info[method_name]['write'][return_id] if tnode.parent == ast.Subscript]
                #currently only process with situation that return_value is only written once
                if len(write_return == 0):
                    pass           
    except:
        pass"""