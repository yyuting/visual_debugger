import ast_node_visitor
import ast
import sys
from astmonkey import transformers
from sympy.parsing.sympy_parser import parse_expr
import astunparse
import visualize
import get_type
import get_edge
import os
import z3
import redbaron
from util import RedBaron

def rewrite_expr_z3(r, is_redbaron=True):
    # Rewrites RedBaron expression to a str expression that could be used in z
    # Return (z3_expr_str, z3_varnames)
    z3_expr_str = (r.dumps() if is_redbaron else r).strip()
    z3_expr_str = z3_expr_str.replace('.', '_').replace('[', '_').replace(']', '_')
 
    rp = RedBaron(z3_expr_str)
    for node in rp.find_all('UnitaryOperatorNode'):
        if node.value == 'not':
            node.replace('z3.Not(' + node.target.dumps() + ')')
    for node in rp.find_all('BooleanOperatorNode'):
        if node.value == 'and':
            node.replace('z3.And(' + node.first.dumps() + ',' + node.second.dumps() + ')')
        elif node.value == 'or':
            node.replace('z3.Or(' + node.first.dumps() + ',' + node.second.dumps() + ')')
    z3_expr_str = rp.dumps()
            
    z3_vars = set()
    for node in rp.find_all('NameNode'):
        z3_vars.add(node.value)
    return (z3_expr_str, z3_vars)

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

def is_initialization(nodes):
    """
    check if it's sentences like a = numpy.zeors()
    """
    flag = False
    
    for node in nodes:
        if isinstance(node, ast.Name) and (node.id == 'numpy' or node.id == 'np'):
            flag = True
            break
    return flag

def get_condition(node, read_nodes, lo_L, hi_L, var_L, chosen_radius_L, all_z3_vars):
    
    radius_r = chosen_radius_L[0]
    radius_c = chosen_radius_L[1]
    var_r = var_L[0]
    var_c = var_L[1]
    
    conditions = {}
    
    for read_node in read_nodes:
        ifnode = None
        parent = read_node.parent
        while parent is not None:
            if isinstance(parent, ast.If):
                ifnode = parent
                break
            elif isinstance(parent, ast.For):
                break
            parent = parent.parent
       
        if ifnode is not None:
           
            #conditional_s = astunparse.unparse(ifnode.test)[0 : -1]
            for j in range(3):
                for k in range(3):
                    for prove_true in [False, True]:
                        conditional_s = astunparse.unparse(ifnode.test)[0 : -1]
                        if j == 0:
                            lo_r = lo_L[0].dumps()
                            hi_r =  '(' + '(' + lo_r + ') + ' + radius_r + ')'
                            lo_r_extra = lo_r
                            hi_r_extra = '(' + '(' + hi_L[0].dumps() + ') - ' + radius_r + ')'
                       
                        elif j == 1:
                            lo_r = '(' + '(' + lo_L[0].dumps() + ') + ' + radius_r + ')'
                            hi_r = '(' + '(' + hi_L[0].dumps() + ') - ' + radius_r + ')'
                            lo_r_extra = lo_r
                            hi_r_extra = hi_r
                            
                        elif j == 2:
                            lo_r = '(' + '(' + hi_L[0].dumps() + ') - ' + radius_r + ')'
                            hi_r = hi_L[0].dumps()
                            lo_r_extra = '(' + '(' + lo_L[0].dumps() + ') + ' + radius_r + ')'
                            hi_r_extra = hi_r
                            
                        if k == 0:
                            lo_c = lo_L[1].dumps()
                            hi_c = '(' + '(' + lo_c + ') + ' + radius_c + ')'
                            lo_c_extra = lo_c
                            hi_c_extra = '(' + '(' + hi_L[1].dumps() + ') - ' + radius_c + ')'
                            
                        elif k == 1:
                            lo_c = '(' + '(' + lo_L[1].dumps() + ') + ' + radius_c + ')'
                            hi_c = '(' + '(' + hi_L[1].dumps() + ') - ' + radius_c + ')'
                            lo_c_extra = lo_c
                            hi_c_extra = hi_c
                            
                        elif k == 2:
                            lo_c = '(' + '(' + hi_L[1].dumps() + ') - ' + radius_c + ')'
                            hi_c = hi_L[1].dumps()
                            lo_c_extra = '(' + '(' + lo_L[1].dumps() + ') + ' + radius_c + ')'
                            hi_c_extra = hi_c
                            
                        current_z3_vars = {}
                        for z3_var in all_z3_vars:
                            current_z3_vars[z3_var] = z3.Int(z3_var)
                                
                        lo_constraint_r = rewrite_expr_z3('{var_r} >= {lo_r}'.format(**locals()), False)[0]
                        hi_constraint_r = rewrite_expr_z3('{var_r} < {hi_r}'.format(**locals()), False)[0]
                        lo_constraint_r_extra = rewrite_expr_z3('{var_r} >= {lo_r_extra}'.format(**locals()), False)[0]
                        hi_constraint_r_extra = rewrite_expr_z3('{var_r} < {hi_r_extra}'.format(**locals()), False)[0]
                    
                        lo_constraint_c = rewrite_expr_z3('{var_c} >= {lo_c}'.format(**locals()), False)[0]
                        hi_constraint_c = rewrite_expr_z3('{var_c} < {hi_c}'.format(**locals()), False)[0]
                        lo_constraint_c_extra = rewrite_expr_z3('{var_c} >= {lo_c_extra}'.format(**locals()), False)[0]
                        hi_constraint_c_extra = rewrite_expr_z3('{var_c} < {hi_c_extra}'.format(**locals()), False)[0]
                                
                        solver = z3.Solver()
                        solver.add(eval(lo_constraint_r, globals(), current_z3_vars))
                        solver.add(eval(hi_constraint_r, globals(), current_z3_vars))
                        solver.add(eval(lo_constraint_c, globals(), current_z3_vars))
                        solver.add(eval(hi_constraint_c, globals(), current_z3_vars))
                        solver.add(eval(lo_constraint_r_extra, globals(), current_z3_vars))
                        solver.add(eval(hi_constraint_r_extra, globals(), current_z3_vars))
                        solver.add(eval(lo_constraint_c_extra, globals(), current_z3_vars))
                        solver.add(eval(hi_constraint_c_extra, globals(), current_z3_vars))
                        
                        if prove_true:
                            conditional_s = 'not (' + conditional_s + ')'
                        conditional_s = rewrite_expr_z3(conditional_s, False)[0]
                        
                        conditional_eval = eval(conditional_s, globals(), current_z3_vars)
                        solver.add(conditional_eval)
                            
                        if solver.check() == z3.unsat:
                            conditions.setdefault(read_node, []).append((j, k, prove_true))
                            break
                       
    return conditions

if __name__ == "__main__":
    
    path = 'blur_test.py'
    method_name = 'gaussian_blur'
    
    #path = 'blur_two_stage.py'
    #method_name = 'two_stage_blur'
    
    source = open(path, 'rt').read()
    node = ast.parse(source)
    node = transformers.ParentNodeTransformer().visit(node)
    visitor = ast_node_visitor.DependencyVisitor()
    visitor.visit(node)
    
    local_types = get_type.get_types(os.getcwd(), source)
    
    (lo_Ls, hi_Ls, var_Ls, chosen_radius_Ls, all_z3_vars) = get_edge.get_edge(source, local_types, method_name)
    
    #visualize.display_output_and_click(local_types['test_result'], node, visitor, chosen_radius_Ls, all_z3_vars)
    
    radius_r = chosen_radius_Ls[-1][0]
    radius_c = chosen_radius_Ls[-1][1]
    
    return_nodes = [tnode for tnode in visitor.def_info[method_name]['return'] 
                    if tnode.id in visitor.def_info[method_name]['array']]

    for return_node in return_nodes:
    
        write_nodes = visitor.def_info[method_name]['write'][return_node.id]
    
        for write_node in write_nodes[::-1]:
            
            if not is_initialization(visitor.def_info[method_name]['write_to_read'][write_node]):
                
                #read_nodes = [tnode for tnode in visitor.def_info[method_name]['write_to_read'][write_node] 
                 #             if tnode.id in visitor.def_info[method_name]['array']]
                
                read_nodes=[tnode for tnode in visitor.find_backward_dependency(write_node, []) 
                             if tnode.id in visitor.def_info[method_name]['array'] and tnode.id != write_node.id]
                
                condition = get_condition(node, read_nodes, lo_Ls[0], hi_Ls[0], var_Ls[0], chosen_radius_Ls[0], all_z3_vars)
                
                visualize.display_output_and_click(local_types, var_Ls[0], chosen_radius_Ls[0], read_nodes, condition)
                
                if len(read_nodes):
                    direction = find_direction(write_node, read_nodes[::-1])
                    #visualize.animate_input_output(direction=direction)
                    visualize.animate_input_output_edge(direction=direction, radius_r=int(radius_r), radius_c=int(radius_c))
                    #visualize.animate_input_output_edge_condition_check(direction=direction, radius_r=int(radius_r), radius_c=int(radius_c), condition=condition, read_nodes=read_nodes)