import redbaron
import hashlib
import os
import sys
import importlib
import pickle

compile_filename_prefix = '_compile_'
python_headers = """
import util
import numpy
""" + '\n'

class RunFailed(Exception):
    pass

def is_test_funcname(funcname):
    """
    Returns True if the given function name str funcname is a test function.
    """
    return funcname.startswith('test')

def indent(s, nspaces):
    space_str = ' ' * nspaces
    lines = s.split('\n')
    return '\n'.join(space_str + line for line in lines)

def remove_if_exists(filename):
    if os.path.exists(filename):
        os.remove(filename)

def run_code(path, source):
    """
    Run code, wrapping it in a subprocess.
    """
    
    try:
        ans_d = run_code_subprocess(path, source)
        ans = ans_d['ans']
        return ans
    finally:
        pass
    
def run_code_subprocess(path, source, clean=True, verbose=None, cython=True, extra_info=None, clean_on_fail=False, verbose_on_fail=True, is_initial_run=False, repeats=1, once=False, out_filename=None, override_input_image=None, override_n_tests=None, override_args=None, override_kw_args=None, use_4channel=False):
    """
    Run code without wrapping in a subprocess.
    
    Given source code string for a module, Cython-ize it (or use Python if cython is False), change directory to 'path', and report the result of module.test().
    
    On failure raises RunFailed exception.
    """ 
#    source = insert_initial_run_info(source, is_initial_run)
    
    prefix = compile_filename_prefix + hashlib.md5(pickle.dumps(repr((source, cython)))).hexdigest()
    orig = os.getcwd()
    old_path = list(sys.path)
    success = False
    try:
        try:
            with open(prefix + '.py', 'wt') as f:
                f.write(python_headers + source)
            assert os.path.exists(prefix + '.py'), 'file missing:' + prefix + '.py'
            os.chdir(path)
            sys.path.append(path)
            importlib.invalidate_caches()           # If we do not clear the caches then module will sometimes not be found
            mod = importlib.import_module(prefix)
            for j_repeat in range(repeats):
                ans = mod.test()
            success = True
            
        except (SystemExit, Exception) as e:
            raise RunFailed(str(e))
    finally:
        sys.path = old_path
        os.chdir(orig)
        
        if (success and clean) or ((not success) and clean_on_fail):
            remove_if_exists(prefix + '.py')

    return {'ans': ans}

def get_types(path, source):
    """
    Get types used by all functions.
    
    Modifies source so each defined function tracks return types before it returns.
    Returns dict with run info. The key 'types' in the run info dict stores a dict mapping
    function name to a list of type configurations used for each function, where a type
    configuration is a dict mapping local variable name => type.
    """
    r = redbaron.RedBaron(source)

    macroL = []
    
    # Tag RedBaron function call and macro nodes
    defnode_id_to_macros = {}
    macro_id_to_defnode = {}
    
    L = r.find_all('DefNode')

    def get_arg_names(node):
        return [_arg.name.value for _arg in node.arguments]

    func_name_to_argnames = {}

    names = []
    for node in L:
        if not is_test_funcname(node.name):
            names.append(node.name)
#            node.value = 'try:\n' + node.value.dumps() + '\nfinally:\n    global {}_locals\n    try:\n        {}_locals\n    except:\n        {}_locals = set()\n    print("locals var:", {}_locals)\n    {}_locals.add(frozenset([(_k, util.get_cython_type(_v)) for (_k, _v) in locals().items()]))\n'.format(node.name, node.name, node.name, node.name, node.name)
            name = node.name
            node_str = node.value.dumps()
            
            decode_argtypes_L = []

            decode_argtypes = '\n'.join(decode_argtypes_L)
            
            arg_names = get_arg_names(node)
            func_name_to_argnames[name] = arg_names
            
            node.value = \
"""_argtype_values = {{}}
def _log_argtype_value(id_num, v):
    try:
        if type(v) == type(_argtype_values[id_num]):
            return v
    except KeyError:
        _argtype_values[id_num] = v
        return v
    _argtype_values[id_num] = util.promote_numeric(_argtype_values[id_num], v)
    return v
try:
{node_str}
finally:
    global _{name}_locals
    try:
        _{name}_locals
    except:
        _{name}_locals = util.TypeSignatureSet({arg_names})
    _ignore_names = ['_log_argtype_value', '_argtype_values', '_ignore_names']
    _locals_typeconfig = dict([(_k, util.CythonType.from_value(_v, None, error_variable=_k)) for (_k, _v) in locals().items() if _k not in _ignore_names])
{decode_argtypes}
    _{name}_locals.add(_locals_typeconfig)
""".format(**locals())

    for node in L:
        if node.name == 'test':
            globalL = ['_{}_locals'.format(k) for k in names] # + ['_{}_argtypes'.format(k) for k in names]
            typesL_updateL = []
            for k in names:
                locals_name = '_{}_locals'.format(k)
                arg_names = func_name_to_argnames[k]
#                typesL_updateL.append('print(_{}_locals)'.format(k))
                typesL_updateL.append('if "{locals_name}" in globals(): _typesL_var["{k}"] = util.TypeSignatureSet({arg_names}, [{{_k: _v for (_k, _v) in _typeconfig.items() if isinstance(_k, str)}} for _typeconfig in {locals_name}])'.format(**locals()))
#            types_dL = ["'{}': _{}_locals".format(k, k) for k in names]
#            node.value = 'try:\n' + node.value.dumps() + '\nfinally:\n    global {}\n    ans = {{{}}}\nreturn ans'.format(','.join(globalL), ','.join(dL))
            node_str = indent(node.value.dumps(), 4)
            globalL_str = ','.join(globalL)
            typesL_update_str = '\n        '.join(typesL_updateL)
            
            node.value = \
"""_exc = None
try:
    def inner_func():
        {node_str}
    ans = inner_func()
except Exception as _e:
    _exc = _e
finally:
    if _exc is not None:
        raise _exc
    else:
        global {globalL_str}
        _typesL_var = {{}}
        {typesL_update_str}
        return {{"types": _typesL_var, "test_result": ans}}
""".format(**locals())

#        _typesL_var = {{_k: _v for (_k, _v) in _typesL_var.items() if isinstance(_k, str)}}

    s = r.dumps()
    
    result = run_code(path, s)


#    ans = {}
#    for func in result:
#        ans_typeconfigL = []
#        for typeconfig in result[func]:
#            sub = {}
#            for (key, value) in result[func].items():
#                sub[key] = get_cython_type(value)
#            ans_typeconfigL.append(sub)
#        ans[func] = ans_typeconfigL
#    return ans
    return result