import ast

class DependencyVisitor(ast.NodeVisitor):
    """
    This is a visitor that reads all the namenodes on either side of the assignment node, then it creates a dependency graph (forward and backward) for the source code
    """
    def __init__(self):
        self.read = {}  #just cache
        self.write = {} #just cache
        self.write_to_read = {} #just cache
        self.forward_graph = {}
        self.backward_graph = {}
        self.array_name = [] #just cache
        self.flag = None
        self.lhs = None
        self.rhs = None
        self.sort_nodes_by_name = {}
        self.def_info = {}
        self.returns = [] #just cache
        
    def visit_Return(self, node):
        
        self.returns.append(node.value)
        super(DependencyVisitor, self).generic_visit(node)
    
    
    def visit_FunctionDef(self, node):
        """
        clears lhs and rhs, creates new forward and backward graph, 'cos variables are in different scale now
        """
        
        self.read = {}
        self.write = {}
        self.write_to_read = {}
        self.array_name = []
        self.returns = []
        super(DependencyVisitor, self).generic_visit(node)
        self.def_info[node.name] = {'node': node, 'write': self.write, 'write_to_read': self.write_to_read, 'array': self.array_name, 'return':self.returns}
    
    def visit_Assign(self, node):
        """
        connects the lhs and rhs for each assignment
        """
        self.lhs = []
        self.rhs = []
        
        for field, value in ast.iter_fields(node):
            
            if field == 'targets':
                self.flag = 'lhs'
            elif field == 'value':
                self.flag = 'rhs'
                
            if isinstance(value, list):
                for item in value:
                    if isinstance(item, ast.AST):
                        self.visit(item)
            elif isinstance(value, ast.AST):
                self.visit(value)
            
            self.flag = None
        
        for write_node in self.lhs:
            self.write_to_read.setdefault(write_node, self.rhs)
        
        self.lhs = None
        self.rhs = None
        
    def visit_AugAssign(self, node):
        """
        connects the lhs and rhs for each assignment
        """
        self.lhs = []
        self.rhs = []
        
        for field, value in ast.iter_fields(node):
            
            if field == 'target':
                self.flag = 'aug_lhs'
            elif field == 'value':
                self.flag = 'rhs'
                
            if isinstance(value, list):
                for item in value:
                    if isinstance(item, ast.AST):
                        self.visit(item)
            elif isinstance(value, ast.AST):
                self.visit(value)
            
            self.flag = None
        
        for write_node in self.lhs:
            self.write_to_read.setdefault(write_node, self.rhs)
        
        self.lhs = None
        self.rhs = None
        
    def visit_Index(self, node):
        """
        don't count index as write, only count them as read
        """
        try:
            self.cache = self.flag
            self.flag = None
            super(DependencyVisitor, self).generic_visit(node)
            self.flag = self.cache
            self.cache = None
        except:
            super(DependencyVisitor, self).generic_visit(node)

    def visit_Subscript(self, node):
        """
        tag variables that are followed by index as array
        """
        try:
            if node.value.id not in self.array_name:
                self.array_name.append(node.value.id)
        except:
            pass
        
        super(DependencyVisitor, self).generic_visit(node)
    
    def visit_Name(self, node):
        """
        connects namenodes if they're in the same assignment node or if they have the same name
        """
        if self.flag is not None:
            
            if self.flag == 'lhs':
                self.lhs.append(node)
                if self.rhs is not None:
                    for i in range(len(self.rhs)):
                        self.connectgraph(node, self.rhs[i])
                self.write.setdefault(node.id, []).append(node)
            
            elif self.flag == 'rhs':
                self.read[node.id] = node
                self.connectname(node)
                self.rhs.append(node)
                if self.lhs is not None:
                    for i in range(len(self.lhs)):
                        self.connectgraph(self.lhs[i], node)
                        
            elif self.flag == 'aug_lhs':
                self.lhs.append(node)
                if self.rhs is not None:
                    for i in range(len(self.rhs)):
                        self.connectgraph(node, self.rhs[i])
                if node.id in self.write:
                    for write_node in self.write[node.id]:
                        self.connectgraph(node, write_node)
                self.write.setdefault(node.id, []).append(node)
                        
        else:
            if isinstance(node.ctx, ast.Store):
                if self.lhs is not None:
                    self.lhs.append(node)
                    if self.rhs is not None:
                        for i in range(len(self.rhs)):
                            self.connectgraph(node, self.rhs[i])
                self.write.setdefault(node.id, []).append(node)
                
            elif isinstance(node.ctx, ast.Load):
                self.read[node.id] = node
                self.connectname(node)
                if self.rhs is not None:
                    self.rhs.append(node)
                    if self.lhs is not None:
                        for i in range(len(self.lhs)):
                            self.connectgraph(self.lhs[i], node)

    def connectgraph(self, node1, node2):
        """
        node1 is dependent of node2. eg: node1 = node2 in source code
        """
        forward_edge = self.forward_graph.setdefault(node2, [])
        
        if node1 not in forward_edge:
            self.forward_graph[node2].append(node1)
        
        if node1 not in self.forward_graph:
            self.forward_graph.setdefault(node1, [])
        
        backward_edge = self.backward_graph.setdefault(node1, [])
        
        if node2 not in backward_edge:
            self.backward_graph[node1].append(node2)
        
        if node2 not in self.backward_graph:
            self.backward_graph.setdefault(node2, [])
            
    def connectname(self, node):
        """
        node is a read, connect dependency between node and every namenode that has the same variable name as node
        """
        name = node.id
        if name in self.write:
            writenodes = self.write[node.id]
            if writenodes is not None:
                if self.lhs is None:
                    for i in range(len(writenodes)):
                        self.connectgraph(node, writenodes[i])
                else:
                    for i in range(len(writenodes)):
                        if writenodes[i] not in self.lhs:
                            self.connectgraph(node, writenodes[i])

    def find_forward_dependency(self, node, result):
        """
        find all nodes that is dependent on node
        """
        if node in self.forward_graph:
            dependent_nodes = self.forward_graph[node]
            for i in range(len(dependent_nodes)):
                if dependent_nodes[i] not in result:
                    result.append(dependent_nodes[i])
                    result = self.find_forward_dependency(dependent_nodes[i], result)
                    
        return result
    
    def find_backward_dependency(self, node, result):
        """
        find all nodes that is dependent on node
        """
        if node in self.backward_graph:
            dependent_nodes = self.backward_graph[node]
            for i in range(len(dependent_nodes)):
                if dependent_nodes[i] not in result:
                    result.append(dependent_nodes[i])
                    result = self.find_backward_dependency(dependent_nodes[i], result)
                    
        return result
    
    def print_forward_graph(self):
        """
        print the graph in a reader-friendly way
        """
        for i, nodes in self.forward_graph.items():
            node_tuple = [i.id, i.lineno, i.col_offset]
            print(node_tuple, end="")
            print('-------------------')
            for node in nodes:
                node_tuple = [node.id, node.lineno, node.col_offset]
                print(node_tuple, end="")
            print()
            
    def print_backward_graph(self):
        """
        print the graph in a reader-friendly way
        """
        for i, nodes in self.backward_graph.items():
            node_tuple = [i.id, i.lineno, i.col_offset]
            print(node_tuple, end="")
            print('-------------------')
            for node in nodes:
                node_tuple = [node.id, node.lineno, node.col_offset]
                print(node_tuple, end="")
            print()
            