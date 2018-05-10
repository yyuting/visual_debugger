import get_type
import numpy
import z3
import util
from util import RedBaron
import redbaron

min_radius = 0
max_radius = 5

class LoopRemoveConditionalsProofFailed(Exception):
    pass

def get_edge(s, local_types, method_name):
    
    local_types = list(local_types['types'][method_name].s.values())[0]
        
    r = RedBaron(s)

    defnodes = [tnode for tnode in util.find_all(r, 'DefNode') if tnode.name == method_name]
    defnode = defnodes[0]

    base_fornodes = util.find_fornodes(r)
    
    lo_Ls = []
    hi_Ls = []
    var_Ls = []
    chosen_radius_Ls = []
    conditionals = []
    
    
    for base_fornode in base_fornodes:
        
        # Find one or more continuous for loops inside which all other code blocks are nested
        all_fornode_L = base_fornode.find_all('ForNode')
        fornode_L = []
        for (i, fornode) in enumerate(all_fornode_L):
            fornode_L.append(fornode)
            subnodes = [node for node in fornode.value if not isinstance(node, redbaron.CommentNode)]
            if len(subnodes) == 1 and i+1 < len(all_fornode_L) and subnodes[0] == all_fornode_L[i+1]:
                pass
            else:
                break
        
        # For each such for loop, identify variable name, lower, upper bounds
        
        assert len(fornode_L)
        if not all(isinstance(x.iterator, redbaron.NameNode) for x in fornode_L):
            raise TransformError('each for loop must have a single var for LoopRemoveConditionals')
        var_L = [x.iterator.name.value for x in fornode_L]
        lo_L = []
        hi_L = []
        zero = RedBaron('0').find_all('IntNode')[0]
        
        is_parallel_L = []
        
        for fornode in fornode_L:
            fornode_value_str = fornode.target.value.name.value
            if len(fornode.target.value) >= 3 and [fornode.target.value[j].value for j in range(3)] == ['cython', 'parallel', 'prange']:
                is_parallel = True
            elif fornode_value_str in ['range', 'xrange']:
                is_parallel = False
            else:
                raise TransformError('each for loop must have range or xrange for LoopRemoveConditionals ({})', fornode_value_str)
            is_parallel_L.append(is_parallel)

            # Get positional arguments
            call_L = [c.value for c in fornode.target.value.call if c.target is None]
            if len(call_L) == 1:
                lo_L.append(zero)
                hi_L.append(call_L[0])
            elif len(call_L) == 2:
                lo_L.append(call_L[0])
                hi_L.append(call_L[1])
            elif len(call_L) == 3:
                success = False
                if util.is_int_constant(call_L[2].dumps()): #isinstance(call_L[2], (redbaron.FloatNode, redbaron.IntNode)) or (isinstance(call_L[2], redbaron.UnitaryOperatorNode) and isinstance(call_L[2].target, (redbaron.FloatNode, redbaron.IntNode))):
                    val = eval(call_L[2].dumps())
                    if val == 1:
                        lo_L.append(call_L[0])
                        hi_L.append(call_L[1])
                        success = True

                if not success:
                    raise TransformError('for loop range currently must have constant step of exactly 1 to apply LoopRemoveConditionals')
            else:
                raise TransformError('for loop range must have 1 to 3 arguments to apply LoopRemoveConditionals')

        # Get z3 expression strings
        
        lo_z3_L = []
        hi_z3_L = []

        def rewrite_expr_z3(r, is_redbaron=True):
            # Rewrites RedBaron expression to a str expression that could be used in z3
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
        
        all_z3_vars = set(var_L)
        for i in range(len(lo_L)):
            (lo_z3, z3_vars) = rewrite_expr_z3(lo_L[i])
            all_z3_vars |= z3_vars
            (hi_z3, z3_vars) = rewrite_expr_z3(hi_L[i])
            all_z3_vars |= z3_vars
            lo_z3_L.append(lo_z3)
            hi_z3_L.append(hi_z3)

        # Find all array getitem/setitem expressions (e.g. a[y,x])
        getitem_L = []

        for node in base_fornode.find_all('AtomtrailersNode'):
            if len(node) == 2 and isinstance(node.value[0], redbaron.NameNode) and isinstance(node.value[1], redbaron.GetitemNode):
                getitem_L.append(node)
        
        # For each dimension j of each expression of an array A, find radius r_j such that we can prove that the expression is always in bounds if we are more than r_j away from edge of array. Associate r_j with corresponding for loop dimension i (i.e. var_L[i]).

        # List of all candidate radii
        radius_L = [str(rval) for rval in range(min_radius, max_radius+1)]
        radius_set = set(radius_L)

        getitem_arrayname_args_L = []
        for getitem_node in getitem_L:
            arrayname = getitem_node.value[0].value
            args = getitem_node.getitem.value
            if not isinstance(args, redbaron.TupleNode):
                args = [args]
            args = list(args)
            getitem_arrayname_args_L.append((getitem_node, arrayname, args))

            for arg in args:
                for current_node in util.all_nodes(arg):
                    try:
                        current_z3 = rewrite_expr_z3(current_node)[0].strip()
                    except:
                        continue
                    if len(current_z3):
                        if current_z3 not in radius_set:
                            radius_set.add(current_z3)
                            radius_L.append(current_z3)

        # Intersection of success radii from each dimension
        success_radius_intersect_L = [set(radius_L) for j in range(len(var_L))]

        def get_bound(i, is_upper, radius='0'):
            bound = lo_z3_L[i] if not is_upper else hi_z3_L[i]
            ineq = '>=' if not is_upper else '<'
            pad = ('+' if not is_upper else '-') + '(' + radius + ')'
            z3_expr = '(' + var_L[i] + ')' + ineq + '((' + bound + ')' + pad + ')'
            return z3_expr
                
        for (getitem_node, arrayname, args) in getitem_arrayname_args_L:
            try:
                
                # Add assumptions that current argument to the array 'arrayname' is out of bounds along dimension j,
                # on either the lower bound side (if is_lo_bound) or else the upper bound side.
                for (j, arg) in enumerate(args):
                    # Skip indices that are greater than the number of loops
                    if j >= len(var_L):
                        continue
                    
                    # Skip getitem index expressions that involve only a single variable, e.g. 'r' and 'c' in A[r,c]
                    if isinstance(arg, redbaron.NameNode):
                        continue

                    success_radius_L = []

                    # Find radii that work out of the list of candidate radii, where we can prove in-bounds property on
                    # both sides.
                    for radius in radius_L:
                        radius_success = True
                        radius_is_constant = util.is_int_constant(radius)

                        arg_s = arg.dumps()
                        for is_lo_bound in [False, True]:
                            if ':' in arg_s:
                                continue

                            solver = z3.Solver()

                            current_z3_vars = {}
                            for z3_var in all_z3_vars:
                                current_z3_vars[z3_var] = z3.Int(z3_var)

                            # Add assumptions that each for loop variable is in bounds, with a distance 'radius' to the edge.
                            i = j
                            for k in range(2):
                                z3_expr = get_bound(i, k, radius)
                                try:
                                    z3_expr_eval = eval(z3_expr, globals(), current_z3_vars)
                                except:
                                    radius_success = False
                                    break
                                    #raise TransformError('LoopRemoveConditionals: could not eval expression {}'.format(z3_expr))
                                solver.add(z3_expr_eval)

                            if not radius_success:
                                break
                            # Add dubious assumption that all arrays with the same shapes during unit testing are always equal in shape.
                            # Really we should probably prove this is true by inspecting the numpy code used and its dependencies
                            # instead of just assuming it.
                            arraytype = local_types[arrayname]
                            for (arrayname_p, arraytype_p) in local_types.items():
                                if (arraytype_p.cython_type == arraytype.cython_type and
                                    arraytype_p.shape_list == arraytype.shape_list):
                                    # It is an array of the same size, so assume equal shape
                                    for k in range(len(arraytype_p.shape)):
                                        z3_var_p = rewrite_expr_z3(arrayname_p + '.shape[{}]'.format(k), False)[0]
                                        z3_var_current = rewrite_expr_z3(arrayname + '.shape[{}]'.format(k), False)[0]
                                        for z3_v in [z3_var_p, z3_var_current]:
                                            if z3_v not in current_z3_vars:
                                                current_z3_vars[z3_v] = z3.Int(z3_v)
                                        
                                        solver.add(eval(z3_var_p, globals(), current_z3_vars) ==
                                                   eval(z3_var_current, globals(), current_z3_vars))

                            # Assume that current variable used in getitem is out of bounds (either too low or too high),
                            # and attempt to derive a contradiction.
                            if is_lo_bound:
                                out_of_bounds = arg_s + ' < 0'
                            else:
                                getitem_hi = rewrite_expr_z3(arrayname + '.shape[{}]'.format(j), False)[0]
                                out_of_bounds = arg_s + ' >= (' + getitem_hi + ')'
                            try:
                                out_of_bounds_eval = eval(out_of_bounds, globals(), current_z3_vars)
                            except:
                                raise LoopRemoveConditionalsProofFailed('LoopRemoveConditionals: could not eval out of bounds expression {}'.format(out_of_bounds))
                            solver.add(out_of_bounds_eval)
                            
                            check = solver.check()
                            if check != z3.unsat:
                                # We did not derive a contraction. This radius is invalid.
                                radius_success = False
                                break
                        
                        if radius_success:
                            success_radius_L.append(radius)
                            
                    success_radius_intersect_L[j] &= set(success_radius_L)
                    
            except LoopRemoveConditionalsProofFailed:
                pass
            
        # Place all constraints in a list
        constraints = []
        for j in range(len(var_L)):
            for k in range(2):
                constraints.append(get_bound(j, k))
        
        # Reduce success_radius_intersect_L to a single radius along each dimension (chosen_radius_L)
        chosen_radius_L = []
        for j in range(len(var_L)):
            success_L = list(success_radius_intersect_L[j])
            is_constant_L = [util.is_int_constant(x) for x in success_L]
            constant_val_L = [(int(success_L[i].strip('()')) if is_constant_L[i] else numpy.nan) for i in range(len(success_L))]
            try:
                min_constant_index = numpy.nanargmin(constant_val_L)
            except ValueError:
                raise TransformError('LoopRemoveConditionals not valid because no radius could be proved')
            success_L = [success_L[min_constant_index]] + [success_L[i] for i in range(len(success_L)) if not is_constant_L[i]]
            
            try:
                chosen_radius_L.append(util.prove_smallest(success_L, all_z3_vars, constraints))
            except util.ProveSmallestError:
                raise TransformError('LoopRemoveConditionals could not prove smallest element')
            
        """loop_body = fornode.value.dumps()
        conditional_status = {}
        
        for nodetype in ['IfNode', 'ElifNode', 'TernaryOperatorNode']:
            for node in fornode.find_all(nodetype):
                conditional = node.test if nodetype != 'TernaryOperatorNode' else node.value
                    
                    #build a grid
                for j in range(3):
                    for k in range(3):
                        for prove_true in [False, True]:
                            
                            radius_r = chosen_radius_L[0]
                            radius_c = chosen_radius_L[1]
                            
                            var_r = var_L[0]
                            var_c = var_L[1]
                            
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
                            
                            conditional_s = conditional.dumps()
                            if prove_true:
                                conditional_s = 'not (' + conditional_s + ')'
                            conditional_s = rewrite_expr_z3(conditional_s, False)[0]
                            
                            conditional_eval = eval(conditional_s, globals(), current_z3_vars)
                            solver.add(conditional_eval)
                            
                            if solver.check() == z3.unsat:
                                conditional_status.setdefault((j, k), []).append((node, prove_true))
                                break"""
        
        lo_Ls.append(lo_L)
        hi_Ls.append(hi_L)
        var_Ls.append(var_L)
        chosen_radius_Ls.append(chosen_radius_L)
        #conditionals.append(conditional_status)
    
    return (lo_Ls, hi_Ls, var_Ls, chosen_radius_Ls, all_z3_vars)

