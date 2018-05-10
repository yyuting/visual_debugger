import numpy
import redbaron
import z3

cython_type_check = True
track_shape_list = False

def RedBaron(s):
    """
    Safe alternative to redbaron.RedBaron() constructor, which fixes the input string passed to the constructor.
    """
    return redbaron.RedBaron(fix_source_redbaron(s))

def fix_source_redbaron(s):
    """
    Fix any RedBaron-created errors in source code that will be subsequently parsed by RedBaron (specifically, lines starting with semicolons).
    """
    ans = []
    
    L = s.split('\n')
    for line in L:
        if line.lstrip().startswith(';'):
            i = line.index(';')
            line = line[:i] + line[i+1:]
        ans.append(line)

    return '\n'.join(ans)

def find_all(r, s):
    """
    Faster implementation of RedBaron find_all() method.
    """
    cls = getattr(redbaron, s)
    return [x for x in all_nodes(r) if isinstance(x, cls)]

def is_int_constant(s):
    """
    Return True if given Python expression is an int constant (but not something that can be simplified to int constant).
    """
    s = s.strip()
    r = redbaron.RedBaron(s)
    int_types = (redbaron.IntNode, redbaron.LongNode, redbaron.OctaNode, redbaron.HexaNode)
    if len(r) == 1:
        node = r[0]
        while isinstance(node, redbaron.AssociativeParenthesisNode):
            node = node.value
        if isinstance(node, redbaron.UnitaryOperatorNode) and node.value in ['-', '+']:
#            print(node.target.help())
            return isinstance(node.target, int_types)
        else:
#            print(node.help())
            return isinstance(node, int_types)
    return False

def find_fornodes(node):
    """
    find outermost for loops in code
    """
    fornodes = [tnode for tnode in find_all(node, 'ForNode')]
    
    i = 1
        
    while len(fornodes) >= i + 1:
        
        current = fornodes[-i].parent
        
        while current is not None:
            
            if current in fornodes:
                del fornodes[-i]
                i -= 1
                break
            else:
                current = current.parent
        #if fornodes[-i].parent in fornodes:
            #del fornodes[-i]
        #else:
            #i += 1
        i += 1
    
    return fornodes

def all_nodes(r):
    """
    Get all nodes (recursively) in redbaron object.
    """
    ans = []
    ans_set = set()
    for node in r._generate_nodes_in_rendering_order():
        node_id = id(node)
        if node_id not in ans_set:
            ans_set.add(node_id)
            ans.append(node)
    return ans

def parent_list(node):
    """
    List of parents of given node.
    """
    ans = []
    current = node
    while current is not None:
        current = current.parent
        if current is not None:
            ans.append(current)
    return ans

class ProveSmallestError(Exception):
    pass

def prove_smallest(L, z3_vars, constraints_L):
    """
    Return element of L which is smallest by using a theorem prover.
    
    Given a list of Python expressions (L), list of all variable names used by those expressions (z3_vars), and list of constraint strings (constraints_L).
    
     Attempts to prove and return the expression that can be proved to always be smaller than all other expressions. If this fails, returns any expression that can be proved to always be less than or equal to other expressions. If that fails, return the first item of the list.
    """
    if len(L) == 0:
        raise ProveSmallestError('expected non-empty list for prove_smallest()')

    always_less = numpy.zeros((len(L), len(L)), 'bool')
    always_leq = numpy.ones((len(L), len(L)), 'bool')

    d = {}
    for var in z3_vars:
        d[var] = z3.Int(var)

    for i in range(len(L)):
        for j in range(len(L)):
            if j == i:
                continue

            # Attempt to prove that L[i] < L[j] always by showing that L[i] >= L[j] causes a contradiction
            s = z3.Solver()
            for constraint in constraints_L:
                try:
                    s.add(eval(constraint, d))
                except:
                    raise ProveSmallestError
            try:
                s.add(eval('({}) >= ({})'.format(L[i], L[j]), d))
            except:
                raise ProveSmallestError
            check = s.check()
            
            always_less[i][j] = (check == z3.unsat)
    
            # Attempt to prove that L[i] <= L[j] always by showing that L[i] > L[j] causes a contradiction
            s = z3.Solver()
            for constraint in constraints_L:
                try:
                    s.add(eval(constraint, d))
                except:
                    raise ProveSmallestError
            try:
                s.add(eval('({}) > ({})'.format(L[i], L[j]), d))
            except:
                raise ProveSmallestError
            check = s.check()
            
            always_leq[i][j] = (check == z3.unsat)

#    print('always_less:')
#    print(always_less)
#    print('always_leq:')
#    print(always_leq)
    
    for (k, A) in enumerate([always_less, always_leq]):
#        print('k=', k)
        for i in range(len(L)):
            all_succeed = True
            for j in range(len(L)):
                if j == i:
                    continue
                if not A[i][j]:
                    all_succeed = False
                    break
            if all_succeed:
                return L[i]

    return L[0]

def promote_numeric(a, b, get_index=False):
    """
    If a and b are numeric types, return the one that has the type of a + b. If not, simply return a.
    
    If get_index is True then return 0 if a was selected, otherwise 1.
    """
    # Promote numeric argument types to a common type
    numeric_types = (bool, int, float, complex, numpy.float32, numpy.float64, numpy.int64, numpy.complex64, numpy.complex128)
    if isinstance(a, numeric_types) and isinstance(b, numeric_types):
        promoted_value = a + b
        if type(a) == type(promoted_value):
            return a if not get_index else 0
        else:
            return b if not get_index else 1
    return a if not get_index else 0

class TypeSignature(dict):
    pass
    #def __hash__(self):
    #    return hash(frozenset(self.items()))
    #
    #def __lt__(self, other):
    #    return sorted(self.items()) < sorted(other.items())

class TypeSignatureSet:
    """
    A sorted set of type signatures for a given function.
    
    A function's type signature is a dict mapping variable name keys to CythonType instances.
    
    When constructed, the TypeSignatureSet needs a list of variable names that are arguments for the function. If a given
    type signature is missing a function variable name then it will not be added.
    """
    def __init__(self, arg_names, L=[]):
        self.arg_names = arg_names
        assert isinstance(self.arg_names, (list, tuple))
        for x in self.arg_names:
            assert isinstance(x, str), 'expected {} to be string'.format(x)
        
        self.s = {}                         # Mapping from argument types to type signatures
        
        for x in L:
            self.add(x)

    def add(self, type_sig, verbose=False):
#    def add(self, type_sig, verbose=True):
        """
        Add type signature to set. If it already exists then update shape of given type signature.
        """
        type_sig = TypeSignature(type_sig)
        #type_sig_key = tuple(sorted([(key, value.cython_type) for (key, value) in type_sig.items()]))
        type_sig_key = []
        for key in self.arg_names:
            if key in type_sig:
                type_sig_key.append(type_sig[key].to_immutable())
            else:
                warnings.warn('type signature is missing function argument {}, so not adding'.format(key))
                return
        type_sig_key = tuple(type_sig_key)
        
        if type_sig_key not in self.s:
            self.s[type_sig_key] = type_sig
        else:
            d = self.s[type_sig_key]
            for key in set(d.keys()) & set(type_sig.keys()):
                d[key].union_inplace(type_sig[key])

    def __len__(self):
        return len(self.s)
        
    def __iter__(self):
        return iter([value for (key, value) in sorted(self.s.items(), key=lambda item: item[0])])
#        return iter(sorted(self.s.values()))

    def __repr__(self):
        return 'TypeSignatureSet({}, [{}])'.format(self.arg_names, ','.join(repr(typesig) for typesig in self.s.values()))
    
class CythonType:
    """
    Constructs both Python and Cython type information from a value.
    
    Instance properties:
        cython_type:     Full Cython type string or other object such as tuple/dict/list (call cython_type_str()
                         to always obtain a single string).
        cython_nickname: Nickname string which can also be used in a C identifier (e.g. a variable name).
        shape:           Numpy array shape. The length is None for any dimension that changes in length.
                         If scalar then shape is ().
        shape_list:      List of all shapes encountered during program run, where each shape is a tuple of ints.
                         If scalar then shape_list is empty. If global variable track_shape_list is False then
                         shape_list is always empty.
    
    CythonType can be constructed using CythonType.from_value() or CythonType.from_cython_type(). These constructors
    take a compiler.ProgramInfo instance (program_info), which has a is_rewrite_float32() method that is used to
    determine whether float64 types should be rewritten to float32 types.
    
    CythonType can be constructed for:
     - Float, int, bool, and string types.
     - Tuple types. In this case, cython_type is a tuple of CythonType instances, cython_nickname is a single nickname
       string that concatenates sub-type nicknames, shape is (n,), where n is the length of the tuple, and shape_list is [(n,)].
     - String type. In this case, cython_type is 'str', cython_nickname is str, shape is (), and shape_list is [()].
     - Dict types. In this case, cython_type is a dict mapping unmodified instances for the dictionary keys to values which
       are CythonType instances constructed from the dictionary values (e.g. CythonType.from_value({'a': 10}) has
       cython_type of {'a': CythonType.from_value(10)}). Also, cython_nickname is a single nickname string that concatenates
       sub-type nicknames, shape is (n,), where n is the dict len, and shape_list is [(n,)].
     - List types. In this case, this list is assumed to homogeneous (of identical type) but arbitrary length that varies
       at run-time. Thus, cython_type is a list of a single CythonType instance storing the element type, cython_nickname
       is a single nickname string which includes the element type, shape is (n,), where n is the known length of the list
       or None if unknown length, and shape_list is [(n,)].
     - Object type, constructed with CythonType.from_value(object(), ...), which indicates a type could not be inferred.
    """
    constant_shape_max_size = 30
    
    promote_primitive_types = {
        ('bool',   'bool' ):     'bool',
        ('int',    'bool' ):     'int',
        ('float',  'bool' ):     'float',
        ('double', 'bool' ):     'double',

        ('bool',   'int'   ):    'int',
        ('int',    'int'   ):    'int',
        ('float',  'int'   ):    'float',
        ('double', 'int'   ):    'double',

        ('bool',   'float' ):    'float',
        ('int',    'float' ):    'float',
        ('float',  'float' ):    'float',
        ('double', 'float' ):    'float',

        ('bool',   'double'):    'double',
        ('int',    'double'):    'double',
        ('float',  'double'):    'double',
        ('double', 'double'):    'double',
    
        ('str', 'str'):          'str',
    }
    
    def equal(self, other, flex_shape=True):
        """
        Equality operator that correctly compares all fields. If flex_shape is True then permit None to equal a known shape size.
        """
        # TODO: Replace comparison operators such as __eq__ with this impleemntation?
        # (But TypeSignature and other places may rely on the currently broken behavior of __eq__, etc, so this has to be done with some care).

        if self.cython_nickname != other.cython_nickname:
            return False
        if flex_shape:
            if len(self.shape) != len(other.shape):
                return False
            if any([self.shape[i] != other.shape[i] and (self.shape[i] is not None and other.shape[i] is not None) for i in range(len(self.shape))]):
                return False
        else:
            if self.shape != other.shape:
                return False
        self_cython_type = self.cython_type
        other_cython_type = other.cython_type
        if isinstance(self_cython_type, str) and isinstance(other_cython_type, str):
            return self_cython_type == other_cython_type
        elif isinstance(self_cython_type, (list, tuple)) and isinstance(other_cython_type, (list, tuple)):
            return self_cython_type[0].equal(other_cython_type[0], flex_shape)
        elif isinstance(self_cython_type, dict) and isinstance(other_cython_type, dict):
            if self_cython_type.keys() != other_cython_type.keys():
                return False
            for key in self_cython_type:
                if not self_cython_type[key].equal(other_cython_type[key], flex_shape):
                    return False
            return True
        return False

    
    def is_subtype(self, other, flex_shape=True):
        """
        Whether self is a subtype of CythonType other.  If flex_shape is True then permit None to equal a known shape size.
        """
#        print('entering is_subtype')
        union_type = union_cython_types(self, other)
#        print('(A) self.shape={}, other.shape={}, union_type.shape={}'.format(self.shape, other.shape, union_type.shape))
#        print('is_subtype: self={}, other={}, union_type={}'.format(self, other, union_type))
#        print('(B) self.shape={}, other.shape={}, union_type.shape={}'.format(self.shape, other.shape, union_type.shape))
        return other.equal(union_type, flex_shape)
    
    def sorted_key_list(self):
        """
        Sorted key list, valid only if dict type (that is, self.is_dict()).
        """
        return sorted(self._cython_type.keys())
    
    def cython_type_str(self, force_non_buffer=False):
        """
        Convert to a single string suitable for cdef type declaration in Cython.
        
        If program_info is a compiler.ProgramInfo instance then adds any relevant Cython class or header declarations
        to program_info.cython_headers. Specifically, cython_headers is a dict, the key is the class name string, and the
        value is the string of the Cython class declaration.
        
        If force_non_buffer is True then the return type string is forced to not be a buffer type (e.g. 'numpy.ndarray'
        instead of 'numpy.ndarray[numpy.float64_t, ndim=2]').
        """
        if self.is_tuple():
            return 'tuple'
        elif self.is_dict():
            if program_info is not None:
                if self.cython_nickname not in program_info.cython_headers:
                    header_str = ['cdef class ' + self.cython_nickname + ':']
                    keys = self.sorted_key_list()
                    for key in keys:
                        assert isinstance(key, str), 'not string key: {}'.format(key)
                        header_str.append('  cdef public ' + self._cython_type[key].cython_type_str(force_non_buffer=True) + ' ' + key)
                    header_str.append('')

                    header_str.append('  def __init__(self, ' + ','.join(keys) + '):')
                    for key in keys:
                        header_str.append('    self.{} = {}'.format(key, key))
                    header_str.append('')

                    header_str.append('  def __getitem__(self, key):')
                    for (i, key) in enumerate(keys):
                        header_str.append('    {} key == {}: return self.{}'.format('if' if i == 0 else 'elif', repr(key), key))
                    header_str.append('    else: raise KeyError(key)')
                    header_str.append('')

                    header_str.append('  def __setitem__(self, key, value):')
                    for (i, key) in enumerate(keys):
                        header_str.append('    {} key == {}: self.{} = value'.format('if' if i == 0 else 'elif', repr(key), key))
                    header_str.append('    else: raise KeyError(key)')
                    header_str.append('')

                    header_str.append('  def __len__(self):')
                    header_str.append('    return {}'.format(self.shape[0]))

                    header_str = '\n'.join(header_str)
                    program_info.cython_headers[self.cython_nickname] = header_str
        
            return self.cython_nickname
        elif self.is_list():
            return 'list'
        if force_non_buffer and isinstance(self._cython_type, str) and '[' in self._cython_type:
            return self._cython_type[:self._cython_type.index('[')]
        return self.rewrite_float32_str(self._cython_type) #self.cython_type

    def rewrite_float32_str(self, s):
        """
        Get cython_type string after optionally rewriting arrays of float64 type to float32 if this has been specified by an ArrayStorage transform.
        """
        if self.is_rewrite_float32():
            if self.is_array():
                if self.primitive_type(rewrite=False) == 'double':
                    return s.replace('float64', 'float32')
        return s
    
    def __init__(self, *args):
        if len(args):
            raise ValueError('Use either CythonType.from_value() or CythonType.from_cython_type()')

    def small_constant_shape(self, max_size=constant_shape_max_size):
        """
        True if has a small and constant shape.
        """
        return len(self.shape) and not any(v is None for v in self.shape) and (max_size is None or all(v <= max_size for v in self.shape))
    
    @staticmethod
    def dim_has_small_constant_shape(v, max_size=constant_shape_max_size):
        return v is not None and (max_size is None or v <= max_size)
    
    scalar_type_to_c = {'float': 'float', 'double': 'double', 'float32': 'float', 'float64': 'double', 'bool': 'bool', 'int': 'int', 'str': 'str', 'int64': 'int64_t'}
    scalar_type_to_numpy = {'float': 'float32', 'double': 'float64', 'float32': 'float32', 'float64': 'float64', 'bool': 'bool', 'int': 'int', 'str': 'str', 'int64': 'int64'}
    
    def set_shape(self, shape):
        """
        Modifies shape.
        """
        if not isinstance(shape, tuple):
            shape = tuple(shape)
        dims_changed = (len(shape) != len(self.shape))
        self.shape = shape
        if dims_changed:
            self.set_primitive_type(self.primitive_type())
    
    def set_primitive_type(self, ptype):
        """
        Set primitive C type string such as 'float', 'double', 'int', for scalar and array types only.
        """
        try:
            ptype_numpy = self.scalar_type_to_numpy[ptype]
            ptype_c = self.scalar_type_to_c[ptype]
        except KeyError:
            raise KeyError('Unknown primitive type {}'.format(ptype))
        if self.shape == ():
            self._cython_type = ptype_c
        elif self.is_array():
            self._cython_type = 'numpy.ndarray[numpy.' + ptype_numpy + '_t, ndim={}]'.format(len(self.shape))
        else:
            raise ValueError('not scalar or array type: {}'.format(self))

    def primitive_type(self, is_numpy=False, allow_complex=True, rewrite=True, cython_type=False):
        """
        Get primitive C type string such as 'float' or 'double', or if is_numpy is True, a numpy type string such as 'float32'.
        
        If cython_type is True then return a CythonType instance instead of a str.
        
        If self is a tuple type then returns a tuple of such primitive C type strings, if allow_complex is True.
        If allow_complex is False, then returns the first primitive C type string from the tuple.
        
        If self is a dict type then returns a dict mapping the original keys to primitive_types, if allow_complex is True.
        If allow_complex is False, then returns the primitive C type string from the smallest key.
        
        If self is a list type then returns a list of a single primitive C type string, if allow_complex is True.
        If allow_complex is False, then returns the first primitive C type string.
        """
        if cython_type:
            return CythonType.from_cython_type(self.primitive_type(is_numpy, allow_complex, rewrite), self.program_info)
        
        def parse_type(t):
            try:
                if not is_numpy:
                    return self.scalar_type_to_c[t]
                else:
                    return self.scalar_type_to_numpy[t]
            except KeyError:
                raise KeyError('Unknown primitive type {}, is_numpy={}, allow_complex={}, rewrite={}, self._cython_type={}, self._cython_nickname={}, self.shape={}'.format(t, is_numpy, allow_complex, rewrite, self._cython_type, self._cython_nickname, self.shape))
        cython_type = self.cython_type if rewrite else self._cython_type
        
        if self.is_array():
            return parse_type(parse_cython_array(cython_type)[1])
        elif self.is_tuple():
#            with open('t.txt', 'wt') as f:
#                f.write(repr(self.cython_type))
            t = tuple([x.primitive_type() for x in cython_type])
            if allow_complex:
                return t
            else:
                return t[0]
        elif self.is_dict():
            t = [(_k, _v.primitive_type()) for (_k, _v) in cython_type.items()]
            if allow_complex:
                return dict(t)
            else:
                return t[0][1]
        elif self.is_list():
            t = [cython_type[0].primitive_type()]
            if allow_complex:
                return t
            else:
                return t[0]
        elif self.is_object():
            return self
        else:
            return parse_type(cython_type)

    def is_tuple(self):
        """
        Returns True if a tuple type.
        """
        return isinstance(self._cython_type, tuple)

    def is_array(self):
        """
        Returns True if a numpy array type.
        """
        return not self.is_tuple() and not self.is_dict() and not self.is_list() and not self.is_str() and not self.is_object() and len(self.shape)

    def is_dict(self):
        """
        Returns True if a dict type.
        """
        return isinstance(self._cython_type, dict)

    def is_list(self):
        """
        Return True if a list type.
        """
        return isinstance(self._cython_type, list)

    def is_str(self):
        return self._cython_type == 'str'
    
    def is_object(self):
        return self._cython_type == 'object'
    
#    def is_numeric(self):
#        return self._cython_type in ['bool', 'int', 'float', 'double'] and len(self.shape) == 0
    
    def c_array_type_suffix(self):
        """
        Get suffix of C array such as '[3]' or '[3][3]'. Raise error if non-constant shape or 0-dimensional.
        """
        assert len(self.shape), 'expected non-zero dimension'
        assert not any(v is None for v in self.shape), 'expected shape to be constant for all dims'
        return ''.join('[{}]'.format(v) for v in self.shape)

    def _set_shape_list(self):
        self.shape_list = [self.shape] if track_shape_list else []

    def _set_dict_info(self):
        self._cython_nickname = '_'.join(value_to_nickname(_k) + '_' + _v.cython_nickname for (_k, _v) in sorted(self._cython_type.items()))
        self.shape = (len(self._cython_type),)
        self._set_shape_list()

    def _set_list_info(self, nelems):
        self._cython_nickname = 'list_' + self._cython_type[0].cython_nickname
        self.shape = (nelems,)
        self._set_shape_list()

    def is_rewrite_float32(self):
        return self.program_info is not None and self.program_info.is_rewrite_float32()

    @property
    def cython_nickname(self):
        return self.rewrite_float32_str(self._cython_nickname)
    
    @cython_nickname.setter
    def cython_nickname(self, value):
        self._cython_nickname = value
    
    @property
    def cython_type(self):
        t = self._cython_type
        if isinstance(t, str):
            return self.rewrite_float32_str(t)
        return t

    @cython_type.setter
    def cython_type(self, value):
        self._cython_type = value

    @staticmethod
    def from_value(value, program_info, error_variable=''):
        """
        Construct from value.
        """
        self = CythonType()
        self.program_info = program_info
        
        if isinstance(value, numpy.ndarray):
            dtype_str = str(value.dtype)
            self._cython_type = 'numpy.ndarray[numpy.{}_t, ndim={}]'.format(dtype_str, value.ndim)
            self._cython_nickname = 'array{}{}'.format(value.ndim, dtype_str)
            self.shape = value.shape
            self._set_shape_list()
            if cython_type_check:
                self.check()
        elif isinstance(value, tuple):
            self.shape = (len(value),)
            L = [CythonType.from_value(x, program_info) for x in value]
            self._cython_nickname = '_'.join(x.cython_nickname for x in L)
            self._cython_type = tuple(L) #tuple([x.cython_type for x in L])
            self._set_shape_list()
            if cython_type_check:
                self.check()
        elif isinstance(value, dict):
            self._cython_type = {_k: CythonType.from_value(_v, program_info) for (_k, _v) in value.items()}
            if not all(isinstance(_k, str) for _k in self.cython_type):
                raise NotImplementedError('CythonType from dict with non-string keys not currently supported: {}'.format(value))
            self._set_dict_info()
            if cython_type_check:
                self.check()
        elif isinstance(value, list):
            if len(value) == 0:
                raise NotImplementedError('unsupported type: empty list')
            self._cython_type = [CythonType.from_value(value[0], program_info)]
            for element in value[1:]:
                self._cython_type[0].union_inplace(CythonType.from_value(element, program_info))
            self._set_list_info(len(value))
        else:
            if isinstance(value, (float, numpy.float64)):
                self._cython_type = 'double'
            elif isinstance(value, (numpy.float32)):
                self._cython_type = 'float'
            elif isinstance(value, (bool, numpy.bool_)):  # This test must be before the int test because, cryptically, isinstance(False, int) is True.
                self._cython_type = 'bool'
            elif isinstance(value, (int, numpy.int64)):
                self._cython_type = 'int'
            elif isinstance(value, str):
                self._cython_type = 'str'
            elif value.__class__ is object().__class__ or value is None:
                self._cython_type = 'object'
            else:
                raise NotImplementedError('unsupported type: {!r} (type: {!r}, error_variable: {})'.format(value, type(value), error_variable))
            self._cython_nickname = self.cython_type
            self.shape = ()
            self.shape_list = []
            if cython_type_check:
                self.check()
        return self
    
    def check(self):
        """
        Run sanity checks for debugging purposes.
        """
#        if len(self.shape) == 1 and self.shape[0] is None:
#            raise ValueError((self.cython_type, self.cython_nickname, self.shape, self.shape_list))
        
        if isinstance(self._cython_type, tuple):
            for x in self._cython_type:
                if isinstance(x._cython_type, str):#, (self.cython_type, self.cython_nickname, self.shape, self.shape_list)
                    if 'shape=' in x._cython_type:
                        raise ValueError((self.cython_type, self.cython_nickname, self.shape, self.shape_list))
        elif isinstance(self._cython_type, list):
            if len(self._cython_type) != 1:
                raise ValueError((self.cython_type, self.cython_nickname, self.shape, self.shape_list))
        else:
            if 'shape=' in self._cython_type:
                raise ValueError((self.cython_type, self.cython_nickname, self.shape, self.shape_list))

    @staticmethod
    def from_cython_type(cython_type_shapeinfo, program_info):
        """
        Construct from cython_type str or tuple (can also include shape info, in the format returned by CythonType.__repr__()).
        """
#        print('from_cython_type({!r})'.format(cython_type_shapeinfo))
        if isinstance(cython_type_shapeinfo, CythonType):
            cython_type_shapeinfo = str(cython_type_shapeinfo)
        is_str = isinstance(cython_type_shapeinfo, str)
        if isinstance(cython_type_shapeinfo, tuple) or (is_str and cython_type_shapeinfo.startswith('(')):
            if isinstance(cython_type_shapeinfo, tuple):
                L_args = cython_type_shapeinfo
            else:
                L_args = eval(cython_type_shapeinfo)
            L = [CythonType.from_cython_type(x, program_info) for x in L_args]
            ans = CythonType()
            ans.program_info = program_info
            ans._cython_type = tuple([x for x in L])
            ans._cython_nickname = '_'.join(x.cython_nickname for x in L)
            ans.shape = (len(L),)
            ans._set_shape_list()
            if cython_type_check:
                ans.check()
            return ans
        elif isinstance(cython_type_shapeinfo, dict) or (is_str and cython_type_shapeinfo.startswith('{')):
            if not isinstance(cython_type_shapeinfo, dict):
                cython_type_shapeinfo = eval(cython_type_shapeinfo)
            L_args = sorted(cython_type_shapeinfo.items())
            ans = CythonType()
            ans.program_info = program_info
            ans._cython_type = {_k: CythonType.from_cython_type(_v, program_info) for (_k, _v) in L_args}
            ans._set_dict_info()
            if cython_type_check:
                ans.check()
            return ans
        elif isinstance(cython_type_shapeinfo, list) or (is_str and (cython_type_shapeinfo.startswith('[') or cython_type_shapeinfo.startswith('"['))):
            if isinstance(cython_type_shapeinfo, list):
                nelems = len(cython_type_shapeinfo)
            elif is_str and (cython_type_shapeinfo.startswith('[') or cython_type_shapeinfo.startswith('"[')):
                if cython_type_shapeinfo.startswith('"') and cython_type_shapeinfo.endswith('"'):
                    cython_type_shapeinfo = cython_type_shapeinfo[1:-1]
                nelems = None
                if 'shape=(' in cython_type_shapeinfo:
                    idx_start0 = cython_type_shapeinfo.rindex('shape=(')
                    idx_start = idx_start0 + len('shape=(')
                    try:
                        comma = cython_type_shapeinfo.index(',', idx_start0)
                        comma_found = True
                    except ValueError:
                        comma_found = False
                    if comma_found:
                        sub = cython_type_shapeinfo[idx_start:comma]
                        try:
                            nelems = int(sub)
                        except ValueError:
                            warnings.warn('could not parse shape field of list in CythonType.from_cython_type() constructor: substring is {}'.format(sub))
                    else:
                        warnings.warn('could not parse shape field of list in CythonType.from_cython_type() constructor')
                    cython_type_shapeinfo = cython_type_shapeinfo[:idx_start0-1]
            else:
                raise ValueError
            if not isinstance(cython_type_shapeinfo, list):
                cython_type_shapeinfo = eval(cython_type_shapeinfo)
            if len(cython_type_shapeinfo) == 0:
                raise ValueError('In CythonType.from_cython_type({!r}), cannot parse length zero list type'.format(cython_type_shapeinfo))
            ans = CythonType()
            ans.program_info = program_info
            ans._cython_type = [CythonType.from_cython_type(cython_type_shapeinfo[0], program_info)]
            ans._set_list_info(nelems)
            if cython_type_check:
                ans.check()
            return ans
        
        cython_type_shapeinfo = cython_type_shapeinfo.strip("'\"")
        self = CythonType()
        self.program_info = program_info
        self._cython_type = cython_type_shapeinfo
        self.shape = None
        self.shape_list = []
        if '(' in self._cython_type and ')' in self._cython_type:
            lparen = self._cython_type.index('(')
            rparen = self._cython_type.rindex(')')
            shapeinfo = self._cython_type[lparen+1:rparen]
            self._cython_type = self._cython_type[:lparen]
#            print('shapeinfo:', shapeinfo)
            try:
                paren_comma = shapeinfo.index('),')
            except ValueError:
                raise ValueError('In CythonType.from_cython_type({!r}), could not find ")," in {!r}'.format(cython_type_shapeinfo, shapeinfo))
            if shapeinfo.startswith('shape=') and shapeinfo[paren_comma+2:].startswith('shape_list='):
                shape_listinfo = shapeinfo[paren_comma+2+len('shape_list='):]
                shapeinfo = shapeinfo[len('shape='):paren_comma+1]
                self.shape = eval(shapeinfo)
                self.shape_list = eval(shape_listinfo) if track_shape_list else []
        if self._cython_type.startswith('numpy.ndarray'):
            (ndim_val, primitive_type) = parse_cython_array(self._cython_type)
            self._cython_nickname = 'array{}{}'.format(ndim_val, primitive_type)
            if self.shape is None:
                self.shape = tuple([None for i in range(int(ndim_val))])
                self.shape_list = []
        else:
            self._cython_nickname = self._cython_type
            if self.shape is None:
                self.shape = ()
                self.shape_list = []

        if cython_type_check:
            self.check()
        return self

    def __repr__(self):
#        print('in __repr__, shape={}, cython_type type: {}'.format(self.shape, type(self.cython_type)))
        if cython_type_check:
            self.check()
        r = self.cython_type
        if isinstance(self.cython_type, tuple):
            return str(r)
        elif isinstance(self.cython_type, dict):
            return '{' + ', '.join(repr(key) + ': ' + repr(value) for (key, value) in sorted(self.cython_type.items())) + '}'
        elif isinstance(self.cython_type, list):
            str_r = str(r)
            if str_r.startswith('["') and str_r.endswith('"]'):
                str_r = '[' + str_r[2:-2] + ']'
            return '"' + str_r + '(shape={})'.format(self.shape) + '"'
        return "'" + r + ('(shape={},shape_list={})'.format(self.shape, self.shape_list) if (len(self.shape) or len(self.shape_list)) else '') + "'"

    def to_immutable(self):
        """
        Return cython_type attribute which has been converted to an immutable (hashable) form that is unique.
        """
        t = self.cython_type
        if isinstance(t, dict):
            t = tuple(sorted(t.items()))
        elif isinstance(t, list):
            t = tuple([t[0], None])
        return t

    def __hash__(self):
        return hash(self.to_immutable())
    
    def __eq__(self, other):
        return self.cython_type == other.cython_type

    def __lt__(self, other):
        return self.cython_type < other.cython_type
    
    def __gt__(self, other):
        return self.cython_type > other.cython_type

    def __le__(self, other):
        return self.cython_type <= other.cython_type

    def __ge__(self, other):
        return self.cython_type >= other.cython_type
    
    def __ne__(self, other):
        return self.cython_type != other.cython_type

    def isinstance_check(self, arg):
        """
        Convert to a code string that checks whether the string arg is an instance of the current Cython type.
        """
        s = self.cython_type #self.cython_type
        if s == 'double':
            return 'isinstance({}, (float, numpy.float64))'.format(arg)
        elif s == 'float':
            return 'isinstance({}, numpy.float32)'.format(arg)
        elif s == 'int':
            return 'isinstance({}, (int, numpy.int64))'.format(arg)
        elif s == 'bool':
            return 'isinstance({}, (bool, numpy.bool_))'.format(arg)
        elif s == 'str':
            return 'isinstance({}, str)'.format(arg)
        elif isinstance(s, str) and s.startswith('numpy.ndarray'):
            (ndim_val, primitive_type) = parse_cython_array(s)
            return '(isinstance({}, numpy.ndarray) and {}.dtype == numpy.{} and {}.ndim == {})'.format(arg, arg, primitive_type, arg, ndim_val)
        elif self.is_tuple():
            return 'isinstance({}, tuple)'.format(arg)
        elif self.is_dict():
            return 'isinstance({}, dict)'.format(arg)
        elif self.is_list():
            return 'isinstance({}, list)'.format(arg)
        else:
            raise ValueError

    def assign_inplace(self, t):
        """
        In-place assignment operator: overwrites properties of self with those of t.
        """
        self._cython_type = t._cython_type
        self._cython_nickname = t._cython_nickname
        self.shape = t.shape
        self.shape_list = t.shape_list
    
    def union_inplace(self, t, warn=True, numeric_promotion=True, numpy_promotion=False):
        """
        Deprecated type union. Please use the function union_cython_types() instead.
        
        Attempt to union in place self with CythonType t, including unioning array shapes and promoting numeric types if needed.
        
        On success, return True. On failure, due nothing, issue a warning (if warn is True), and return False.
        """
#        print('union_inplace({}, {})'.format(self, t))
        p_s = self.primitive_type()
        p_t = t.primitive_type()

        if isinstance(p_s, str) and isinstance(p_t, str):
            try:
                p_promoted = CythonType.promote_primitive_types[(p_s, p_t)]
            except (UnionFailure, KeyError):
                if warn:
                    warnings.warn('could not union types: {}, {}'.format(self, t))
                return False
            if not numeric_promotion:
                if p_promoted != p_s or p_promoted != p_t:
                    if warn:
                        warnings.warn('could not union types in numeric_promotion=False mode: {}, {}'.format(self, t))
                    return False
            if p_promoted == p_t:
                self._cython_type = t._cython_type
                self._cython_nickname = t._cython_nickname
            try:
                self.shape = union_shapes(self.shape, t.shape, numpy_promotion=numpy_promotion)
            except UnionFailure:
                if warn:
                    warnings.warn('could not union shapes: {}, {}'.format(self.shape, t.shape))
                return False
            self.set_primitive_type(p_promoted)
            if track_shape_list:
                self.shape_list.extend(t.shape_list)
        elif isinstance(p_s, tuple) and isinstance(p_t, tuple) and len(p_s) == len(p_t):
            L_s = list(self._cython_type)
            L_t = list(t._cython_type)
            for i in range(len(L_s)):
                L_s[i].union_inplace(L_t[i])
            self._cython_type = tuple(L_s)
        elif isinstance(p_s, dict) and isinstance(p_t, dict) and p_s.keys() == p_t.keys():
            for key in self._cython_type.keys():
                self._cython_type[key].union_inplace(t._cython_type[key])
        elif isinstance(p_s, list) and isinstance(p_t, list) and len(p_s) >= 1 and len(p_t) >= 1:
            self._cython_type[0].union_inplace(t._cython_type[0])
        elif self.is_array() and t.is_list():
            pass
        elif self.is_list() and t.is_array():
            self.assign_inplace(t)
        else:
#            raise ValueError('unknown types for union_inplace: {}, {}'.format(self, t))
            if warn:
                warnings.warn('unknown types for union_inplace: {}, {}'.format(self, t))
            return False
        return True
#        def promote(current_s, current_t):
#            if isinstance(current_s, str) and isinstance(current_t, str):
#                return CythonType.promote_primitive_types[(current_s, current_t)]
#            elif isinstance(current_s, tuple) and isinstance(current_t, tuple) and len(current_s) == len(current_t):
#                return tuple([promote(current_s[i], current_t[i]) for i in range(len(current_s))])
#            elif isinstance(current_s, dict) and isinstance(current_t, dict) and current_s.keys() == current_t.keys():
#                return {_k: promote(current_s[_k], current_t[_k]) for _k in current_s.keys()}
#            else:
#                raise UnionFailure
#        try:
#            p_promoted = promote(p_s, p_t)
#        except UnionFailure:
#            warnings.warn('could not union types: {}, {}'.format(self, t))
#            return