

import sys
from collections import namedtuple

from decaf_lexer import *
from decaf_ast import *

names = {}

precedence = (('right', 'ASSIGN'),
              ('left', 'OR'),
              ('left', 'AND'),
              ('nonassoc', 'EQ', 'NOT_EQ'),
              ('nonassoc', 'LT', 'LTE', 'GT', 'GTE'),
              ('left', 'PLUS', 'MINUS'),
              ('left', 'STAR', 'F_SLASH'),
              ('right', 'UMINUS', 'UPLUS', 'NOT')
              )


# current scope is global. p index tells what index the parents scope is in
# our first child index is at 1. Every time we create a new child, the child will increase
# inner scopes will never clash as it is an invalid name (user cannot define it)
# each variable will be a pointer to an ast node
# index 0 is a stack of our scope path
scope = [[1],{'inner scopes':[]}]

# the current name dictionary we are looking at. When a new dictionary is appended, the p index will be set
# to the current index and the current_index is set to the index of the new appended dictionary.
# current_index = 1

# Every class consist of methods/constructor/parent.
# methods: name: [(param type order, return type, static?, public?)] -- same name methods are put together in a list
# param type order is a list of tuples: (type, formal param name)
# move param type order to next to the name when multiple methods are qllowed
# fields: scope_index, static?, public?
# constructors: (param_types as a tuple or list: public?)

# used to fake these methods. Because we cannot create a node for them.
fake_method = namedtuple('fake_method', ['return_type', 'formals', 's_stat', 'p_stat', 'method_i'])
fake_formals = namedtuple('fake_formals', ['type', 'v_class'])
fake_type = namedtuple('fake_type', ['val', 't_class'])

classes = {
    'In': {
        'methods': {'scan_int':[fake_method('int', [], 1, 1, -1)],
                    'scan_float':[fake_method('float', [], 1, 1, -1)]},
        'constructors': {},
        'fields': {},
        'parent': None,
        'class ref': None
    },
    'Out': {
        'methods': {'print': [fake_method('void', [fake_formals(fake_type('int','constant'), 'formal')], 1, 1, -1),
                              fake_method('void', [fake_formals(fake_type('float','constant'), 'formal')], 1, 1, -1),
                              fake_method('void', [fake_formals(fake_type('boolean','constant'), 'formal')], 1 ,1, -1),
                              fake_method('void', [fake_formals(fake_type('string','constant'), 'formal')], 1, 1, -1)]},
        'constructors': {},
        'fields': {},
        'parent': None,
        'class ref': None
    }
}

primitives = {'int', 'float', 'boolean'}
additional_elementary_types = {'void', 'null'}

current_class = ""
type_to_return = ""
current_method = None


def p_program(p):
    'program : program_header class_decl_list'
    p[2].reverse()
    p[0] = Program(p[2], scope, classes)
    return p[0]

def p_program_header(p):
    'program_header :'
    p[0] = Program_init(scope, classes)

def p_class_decl_list(p):
    '''class_decl_list : class_decl class_decl_list
                       | empty'''

    if len(p) == 2:
        p[0] = []
    else:
        p[2].append(p[1])
        p[0] = p[2]


# EXIT POINT
def p_class_decl(p):
    '''class_decl : class_header LEFT_CB class_body_decl_list RIGHT_CB'''
    p[0] = p[1]
    p[0].ttl_children = 1
    p[0].child1 = p[3]
    p[3].parent = p[0]

    scope[0].pop()

    # calculate class size
    '''size = 0
    for var_ptrs in p[3].class_parts[0]:
        for field in var_ptrs.vars:
            if not field.s_stat:
                field_type = field.type.val
                if str(field_type) == 'int' or str(field_type) == 'boolean' or str(field_type) == 'float':
                    size += 1'''

    # size without parent class
    size = classes[current_class]['class ref'].self_size

    this_class = current_class
    while classes[this_class]['parent'] is not None:
        this_class = classes[this_class]['parent']
        size += classes[this_class]['class ref'].size

    classes[current_class]['class ref'].size = size


# ENTRY POINT
# allows class to be created before body is created
def p_class_header(p):
    '''class_header : CLASS ID
                | CLASS ID EXTENDS ID'''
    global current_class
    current_class = p[2]
    # redefinition of a class
    if current_class in classes:
        # error
        error2(p, 2, "Redefinition of class")
        pass

    # add class to our class list
    classes[current_class] = {'methods': {}, 'constructors': {}, 'fields': {}, 'parent': None, 'class ref': None}

    scope.append({'inner scopes':[]})
    # scope[-1]['p index'] = scope[0]
    scope[0].append(len(scope) - 1)
    scope[scope[0][-2]]['inner scopes'].append(len(scope) - 1)

    # set parent class
    if len(p) == 5:
        classes[current_class]['parent'] = p[4]


    p[0] = Class(p[2])
    # classes[current_class]['class ref'] = p[0]


def p_class_body_decl_list(p):
    'class_body_decl_list : class_body_decl class_body_decl_cont'
    p[2][p[1][0]].append(p[1][1])
    reversed_p2 = [sublist[::-1] for sublist in p[2]]
    p[0] = ClassBody(reversed_p2)


# tuple of list of nodes (can be 0 nodes)
# (list of fields, list of methods, list of constructors)
def p_class_body_decl_cont(p):
    '''class_body_decl_cont : class_body_decl class_body_decl_cont
                            | empty'''
    if p[1] is None:
        p[0] = ([],[],[])
    else:
        p[2][p[1][0]].append(p[1][1])
        p[0] = p[2]


# single node
# each of the declerators are tuples (list to be inserted in, node to insert)
def p_class_body_decl(p):
    '''class_body_decl : field_decl
                       | method_decl
                       | constructor_decl'''
    p[0] = p[1]


def p_field_decl(p):
    'field_decl : modifier var_decl'
    is_static = False
    is_public = False
    if len(p[1]) == 2:
        is_static = True
        if p[1][0] == 'public':
            is_public = True
    elif len(p[1]) == 1:
        if p[1][0] == 'static':
            is_static = True
        elif p[1][0] == 'public':
            is_public = True

    field_nodes = []
    for variable in p[2][1]:
        # make sure the variable has not been declared yet
        if variable not in classes[current_class]['fields']:
            this_node = DummyNodeField(variable, current_class, is_static, is_public, p[2][0])
            field_nodes.append(this_node)
            scope[scope[0][-1]][variable] = this_node
            classes[current_class]['fields'][variable] = this_node

            if not is_static:
                classes[current_class]['class ref'].self_size += 1
            # scope[scope[0][-1]][variable] = (p[1], 'field')
            # classes[current_class]['fields'][variable] = (scope[0][-1], is_static, is_public)
        else:
            # redefinition error
            error2(p, 2, "Redefinition of field")
            pass

    #p[0] = (0,DummyNodeField(p[2],current_class))
    p[0] = (0, DummyNodeVariablePointer(field_nodes))


def p_modifier(p):
    '''modifier : PUBLIC STATIC
                | PRIVATE STATIC
                | PUBLIC
                | PRIVATE
                | STATIC
                | empty'''
    if len(p) == 2:
        p[0] = (p[1],)
    else:
        p[0] = (p[1],p[2])


def p_var_decl(p):
    'var_decl : type variables SEMI_COLON'
    # (type, variable kind (formal/local),)
    p[0] = (p[1],p[2])

    #p[0] = p[2]


def p_type(p):
    '''type : TYPE_INT
            | TYPE_FLOAT
            | TYPE_BOOLEAN
            | ID'''

    # make sure ID is a type
    if p[1] not in classes and p[1] not in primitives:
        # error
        error2(p, 1, "Invalid type")
        pass

    p[0] = p[1]


# list of variables ids
def p_variables(p):
    'variables : variable variables_cont'
    p[2].append(p[1])
    p[0] = p[2]


# list of variable ids
def p_variables_cont(p):
    '''variables_cont : COMMA variable variables_cont
                      | empty'''
    if len(p) == 2:
        p[0] = []
    else:
        p[3].append(p[2])
        p[0] = p[3]


def p_variable(p):
    'variable : ID'
    p[0] = p[1]
    #p[0] = VariableExpr(p[1], p.lineno)


# EXIT POINT
def p_method_decl(p):
    '''method_decl : method_header LEFT_CB stmt_list RIGHT_CB'''

    # pass in the top of the scope stack
    # p[0] = (1, Method(p[1][0], current_class, p[1][2], p[1][1], scope[0][-1], p[3]))
    # p[0] = (2, Method(p[1][0], current_class, classes[current_class]
    # ['methods'][p[1][0]][p[1][1]], p[1][2], scope[0][-1], p[3]))
    # p[1].child1 = p[3]
    # for stmt in p[3]:
    #    stmt.parent = p[1]
    p[3].reverse()
    p[1].child1 = BlockStmt(p[3], p.lineno(3))
    p[1].child1.parent = p[1]

    p[0] = (2, p[1])
    #scope[0] = scope[current_class]['p index']
    scope[0].pop()


# ENTRY POINT
# returns (ID, where method was inserted, formals)
def p_method_header(p):
    '''method_header : modifier type ID LEFT_PN formals RIGHT_PN
                     | modifier TYPE_VOID ID LEFT_PN formals RIGHT_PN'''

    is_static = False
    is_public = False
    if len(p[1]) == 2:
        is_static = True
        if p[1][0] == 'public':
            is_public = True
    elif len(p[1]) == 1:
        if p[1][0] == 'static':
            is_static = True
        elif p[1][0] == 'public':
            is_public = True

    scope.append({'inner scopes':[]})
    scope[0].append(len(scope) - 1)
    scope[scope[0][-2]]['inner scopes'].append(len(scope)-1)

    # (type, variable kind (formal/local))
    formal_nodes = []
    for v_type, name in p[5]:
        if name not in scope[scope[0][-1]]:
            this_var = DummyNodeVariable(v_type, name, 'formal')
            formal_nodes.append(this_var)
            scope[scope[0][-1]][name] = this_var
            # scope[scope[0][-1]][name] = (v_type, 'formal')
        else:
            # error
            error2(p, 5, "Redefinition of formal param")
            pass

    method_node = Method(p[3], current_class, formal_nodes, p[2], is_static, is_public, scope[0][-1])

    #classes[current_class]['methods'][p[3]] = \
    #if p[3] in classes[current_class]['methods']:
        #classes[current_class]['methods'][p[3]].append((p[5], p[2], is_static, is_public))
    #else:
        #classes[current_class]['methods'][p[3]] = [(p[5], p[2], is_static, is_public)]
    classes[current_class]['methods'][p[3]] = [method_node]

    global type_to_return
    global current_method
    type_to_return = TypeNode(p[2], 'constant')
    current_method = method_node

    # (ID, where it was inserted in method array, node of formals)
    # p[0] = (p[3], len(classes[current_class]['methods'][p[3]]) - 1, DummyNodeVariable(p[5], scope[0][-1]))
    p[0] = method_node


# EXIT POINT
# p 1 1 and p 1 2 are unnecessary EXCEPT for printing the AST
def p_constructor_decl(p):
    'constructor_decl : constructor_header LEFT_CB stmt_list RIGHT_CB'
    # p[0] = (1, Constructor(classes[current_class]['constructors'][p[1][1]] ,p[1][0], scope[0][-1], p[3]))
    p[3].reverse()
    p[1].child1 = BlockStmt(p[3], p.lineno(3))
    p[1].child1.parent = p[1]

    p[0] = (1, p[1])
    scope[0].pop()


# ENTRY POINT
# (nodes for formal params, argument types)
def p_constructor_header(p):
    'constructor_header : modifier ID LEFT_PN formals RIGHT_PN'

    if p[2] != current_class:
        # error, constructor name didnt match class name
        error2(p, 2, "Invalid name for constructor of class")
        pass

    argument_types = (item[0] for item in p[4])

    if argument_types in classes[current_class]['constructors']:
        # error, constructor redefinition
        error2(p, 4, "Redefinition of constructor")
        pass

    #is_static = False
    is_public = False
    if len(p[1]) == 2:
        # this is an error constructors cannot be static
        error2(p, 1, "Invalid modifier static for constructor")
        pass
    elif len(p[1]) == 1:
        if p[1][0] == 'static':
            # this is an error constructors cannot be static
            error2(p, 1, "Invalid modifier static for constructor")
            pass
        elif p[1][0] == 'public':
            is_public = True

    scope.append({'inner scopes':[]})
    # scope[-1]['p index'] = scope[0]
    scope[0].append(len(scope) - 1)
    scope[scope[0][-2]]['inner scopes'].append(len(scope) - 1)

    # (type, variable kind (formal/local))
    formal_nodes = []
    for v_type, name in p[4]:
        # check for redefinitions
        if name not in scope[scope[0][-1]]:
            this_node = DummyNodeVariable(v_type, name, 'formal')
            formal_nodes.append(this_node)
            scope[scope[0][-1]][name] = this_node
            # scope[scope[0][-1]][name] = (v_type, 'formal')
        else:
            # error
            error2(p, 4, "Redefinition of formal parameter")
            pass

    # add constructor
    constructor_node = Constructor(formal_nodes, is_public, scope[0][-1])
    classes[current_class]['constructors'][argument_types] = constructor_node

    global type_to_return
    global current_method
    type_to_return = TypeNode('void', 'constant')
    current_method = constructor_node

    p[0] = constructor_node


# list of the params in the order they appear as (type, name)
def p_formals(p):
    '''formals : formal_param formals_cont
               | empty'''
    if len(p) == 2:
        p[0] = []
    else:
        p[2].append(p[1])
        p[0] = p[2]
        p[0].reverse()


def p_formals_cont(p):
    '''formals_cont : COMMA formal_param formals_cont
                    | empty'''
    if p[1] is None:
        p[0] = []
    else:
        p[3].append(p[2])
        p[0] = p[3]


def p_formal_param(p):
    'formal_param : type variable'
    p[0] = (p[1], p[2])


# EXIT POINT
# moves out of current block
def p_block(p):
    'block : block_init LEFT_CB stmt_list RIGHT_CB'
    p[3].reverse()
    p[0] = BlockStmt(p[3],p.lineno(2))
    # scope[0] = scope[scope[0]]['p index']
    scope[0].pop()


# ENTRY POINT
# moves into current block
def p_block_init(p):
    'block_init :'

    scope.append({'inner scopes': []})
    scope[0].append(len(scope) - 1)
    scope[scope[0][-2]]['inner scopes'].append(len(scope) - 1)

    #scope[-1]['p index'] = scope[0]


    variable_buffer = {}


def p_stmt_list(p):
    '''stmt_list : stmt stmt_list
                 | empty'''
    if p[1] is None:
        if len(p) == 2:
            p[0] = []
        else:
            p[0] = p[2]
    else:
        p[2].append(p[1])
        p[0] = p[2]


# returns list of nodes
def p_var_decl_finalize(p):
    '''var_decl_finalize : var_decl'''
    local_nodes = []
    for variable in p[1][1]:
        # make sure the variable has not been declared yet
        if variable not in scope[scope[0][-1]]:
            this_node = DummyNodeVariable(p[1][0], variable, 'local')
            local_nodes.append(this_node)
            scope[scope[0][-1]][variable] = this_node
            # scope[scope[0][-1]][variable] = (p[1], 'local')
        else:
            # redefinition error
            error2(p, 1, "Redefinition of variable")
            pass

    # p[0] = DummyNodeVariable(p[1], scope[0][-1])
    p[0] = DummyNodeVariablePointer(local_nodes)


def p_stmt(p):
    '''stmt : if_stmt
            | while_stmt
            | for_stmt
            | return_stmt
            | stmt_expr_stmt
            | break_stmt
            | continue_stmt
            | block
            | var_decl_finalize
            | semi_colon_stmt'''
    if p[1] is not None:
        p[0] = p[1]
    else:
        p[0] = SkipStmt(p.lineno(1))

def p_if_stmt(p):
    '''if_stmt : IF LEFT_PN expr RIGHT_PN stmt else_stmt'''
    #else_stmt = p[6]

    p[0] = IfStmt(p[3], p[5], p[6], p.lineno(1))


def p_else_stmt(p):
    '''else_stmt : ELSE stmt
                | empty'''
    if len(p) == 2:
        p[0] = SkipStmt(p.lineno(1))
    else:
        p[0] = ElseStmt(p[2], p.lineno(1))


def p_while_stmt(p):
    '''while_stmt : WHILE LEFT_PN expr RIGHT_PN stmt'''
    p[0] = WhileStmt(p[3], p[5], p.lineno(1))


def p_for_stmt(p):
    '''for_stmt : FOR LEFT_PN for_cond1 SEMI_COLON for_cond2 SEMI_COLON for_cond3 RIGHT_PN stmt'''
    p[0] = ForStmt(p[3], p[5], p[7], p[9], p.lineno(1))


def p_for_cond1(p):
    '''for_cond1 : stmt_expr
                 | empty'''
    if p[1] is None:
        p[0] = SkipExpr(p.lineno(1))
    else:
        p[0] = p[1]


def p_for_cond2(p):
    '''for_cond2 : expr
                 | empty'''
    if p[1] is None:
        p[0] = SkipExpr(p.lineno(1))
    else:
        p[0] = p[1]


def p_for_cond3(p):
    '''for_cond3 : stmt_expr
                 | empty'''
    if p[1] is None:
        p[0] = SkipExpr(p.lineno(1))
    else:
        p[0] = p[1]


def p_return_stmt(p):
    '''return_stmt : RETURN return_val SEMI_COLON'''
    p[0] = ReturnStmt(type_to_return, p[2], current_method, p.lineno(1))


def p_return_val(p):
    '''return_val : expr
                  | empty'''
    p[0] = p[1]


def p_stmt_expr_stmt(p):
    '''stmt_expr_stmt : stmt_expr SEMI_COLON'''
    p[0] = ExpressionStmt(p[1], p.lineno(1))


def p_break_stmt(p):
    '''break_stmt : BREAK SEMI_COLON'''
    p[0] = BreakStmt(p.lineno(1))


def p_continue_stmt(p):
    '''continue_stmt : CONTINUE SEMI_COLON'''
    p[0] = ContinueStmt(p.lineno(1))


def p_semi_colon_stmt(p):
    '''semi_colon_stmt : SEMI_COLON'''
    p[0] = SkipStmt(p.lineno(1))


# pay attention to null to see if it is a problem
def p_literal(p):
    '''literal : int_literal
               | float_literal
               | string_literal
               | null_literal
               | boolean_true_literal
               | boolean_false_literal'''
    p[0] = p[1]


def p_int_literal(p):
    '''int_literal : INT_CONST'''
    p[0] = IntegerConstantExpr(p[1], p.lineno(1))


def p_float_literal(p):
    '''float_literal : FLOAT_CONST'''
    p[0] = FloatConstantExpr(p[1], p.lineno(1))


def p_string_literal(p):
    '''string_literal : STRING_CONST'''
    p[0] = StringConstantExpr(p[1], p.lineno(1))


def p_null_literal(p):
    '''null_literal : NULL'''
    p[0] = NullConstantExpr(p.lineno(1))


def p_boolean_true_literal(p):
    '''boolean_true_literal : TRUE'''
    p[0] = BooleanConstantExpr_True(p.lineno(1))


def p_boolean_false_literal(p):
    '''boolean_false_literal : FALSE'''
    p[0] = BooleanConstantExpr_False(p.lineno(1))


def p_primary(p):
    '''primary : literal
               | this
               | super
               | LEFT_PN expr RIGHT_PN
               | NEW ID LEFT_PN arguments RIGHT_PN
               | lhs
               | method_invocation'''
    if len(p) == 2:
        p[0] = p[1]
    elif len(p) == 4:
        p[0] = p[2]
    else:
        if p[2] not in classes:
            # error class we are trying to create does not exist
            error2(p, 2, "Invalid type")
            pass
        # if tuple(p[4]) not in classes[p[2]]['constructors']:
            # error constructor does not exist
            # error2(p, "Invalid constructor arguments")
            # pass
        p[0] = NewObjectExpr(p[2], p[4], current_class, p.lineno(1))


def p_this_primary(p):
    '''this : THIS'''
    p[0] = ThisExpr(current_class, p.lineno(1))


def p_super_primary(p):
    '''super : SUPER'''
    p[0] = SuperExpr(current_class, p.lineno(1))


# put into a list
def p_arguments(p):
    '''arguments : expr arguments_cont
                 | empty'''
    if len(p) == 2:
        p[0] = []
    else:
        p[2].append(p[1])
        p[0] = p[2]
        p[0].reverse()


def p_arguments_cont(p):
    '''arguments_cont : COMMA expr arguments_cont
                      | empty'''
    if len(p) == 2:
        p[0] = []
    else:
        p[3].append(p[2])
        p[0] = p[3]


def p_lhs(p):
    'lhs : field_access'
    p[0] = p[1]


def p_field_access(p):
    '''field_access : primary DOT ID
                    | ID'''

    # verify names exist (choose between creating a variable expr, class reference, expr

    # see if variable is in any of the blocks
    # otherwise class reference expression otherwise error

    def find_var(name):
        for i in range(len(scope[0])-1, -1, -1):
            scope_to_check = scope[scope[0][i]]
            if name in scope_to_check:
                return scope_to_check[name]
        return False

    if len(p) == 2:
        val = find_var(p[1])
        if val:
            p[0] = VariableExpr(val, p.lineno(1))
        else:
            p[0] = ClassReferenceExpression(p[1], p.lineno(1))

    else:
        '''val = find_field(p[3])
        if val:

            # p[0] = FieldAccessExpr(p[1], p[3], p.lineno(1))
            p[0] = FieldAccessExpr(p[1], val, p.lineno(1))
        else:
            # error
            error2(p, 3, "Unitialised field")
            pass'''
        p[0] = FieldAccessExpr(p[1], p[3], current_class, p.lineno(2))


def p_method_invocation(p):
    'method_invocation : primary DOT ID LEFT_PN arguments RIGHT_PN'

    # method exists?
    '''def find_method(name):
        class_counter = p[1].type.val
        while True:
            for method_name in classes[class_counter]['methods'].keys():
                if method_name != p[3]:
                    continue

                methods = classes[class_counter]['methods'][method_name]
                for i in range(len(methods)):
                    formals = methods[i].formals

                    # different amount of arguments / paramaeters
                    if len(formals) != len(p[5]):
                        continue

                    found = True
                    for i, formal in enumerate(formals):
                        if formal.type.val != p[5][i].type.val:
                            found = False
                            break

                    if found:
                        return methods[i]
            if classes[class_counter]['parent'] is None:
                break
            class_counter = classes[class_counter]['parent']

        return None'''
    p[0] = MethodCallExpr(p[1], p[3], p[5], current_class, p.lineno(2))

    '''method_found = find_method(p[3])
    if method_found:
        p[0] = MethodCallExpr(p[1], method_found, p[5], p.lineno(1))
    else:
        # error
        error2(p, 3, "Uninitialised method")
        pass'''


def p_expr(p):
    '''expr : primary
            | assign'''
    p[0] = p[1]


def p_assign(p):
    '''assign : lhs ASSIGN expr
              | post_assign
              | pre_assign'''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = AssignExpr(p[1], p[3], p.lineno(2))


def p_post_assign(p):
    '''post_assign : lhs INCREMENT
                   | lhs DECREMENT'''

    p[0] = AutoExpr(p[1], p[2], 'post', p.lineno(1))


def p_pre_assign(p):
    '''pre_assign : INCREMENT lhs
                   | DECREMENT lhs'''

    p[0] = AutoExpr(p[2], p[1], 'pre', p.lineno(1))


def p_add_expr(p):
    'expr : expr PLUS expr'
    p[0] = BinaryExpr(p[1], p[3], 'add', p.lineno(2))


def p_sub_expr(p):
    'expr : expr MINUS expr'
    p[0] = BinaryExpr(p[1], p[3], 'sub', p.lineno(2))


def p_mult_exp(p):
    'expr : expr STAR expr'
    p[0] = BinaryExpr(p[1], p[3], 'mult', p.lineno(2))


def p_div_expr(p):
    'expr : expr F_SLASH expr'
    p[0] = BinaryExpr(p[1], p[3], 'div', p.lineno(2))


def p_conj_expr(p):
    'expr : expr AND expr'
    p[0] = BinaryExpr(p[1], p[3], 'and', p.lineno(2))


def p_disj_expr(p):
    'expr : expr OR expr'
    p[0] = BinaryExpr(p[1], p[3], 'or', p.lineno(2))


def p_equals_expr(p):
    'expr : expr EQ expr'
    p[0] = BinaryExpr(p[1], p[3], 'eq', p.lineno(2))


def p_notequals_expr(p):
    'expr : expr NOT_EQ expr'
    p[0] = BinaryExpr(p[1], p[3], 'neq', p.lineno(2))


def p_lt_expr(p):
    'expr : expr LT expr'
    p[0] = BinaryExpr(p[1], p[3], 'lt', p.lineno(2))


def p_lte_expr(p):
    'expr : expr LTE expr'
    p[0] = BinaryExpr(p[1], p[3], 'lte', p.lineno(2))


def p_gt_expr(p):
    'expr : expr GT expr'
    p[0] = BinaryExpr(p[1], p[3], 'gt', p.lineno(2))


def p_gte_expr(p):
    'expr : expr GTE expr'
    p[0] = BinaryExpr(p[1], p[3], 'gte', p.lineno(2))


def p_pos_expr(p):
    'expr : PLUS expr %prec UPLUS'
    p[0] = UnaryExpr(p[1], p[2], p.lineno(1))


def p_minus_expr(p):
    'expr : MINUS expr %prec UMINUS'
    p[0] = UnaryExpr(p[1], p[2], p.lineno(1))


def p_not_expr(p):
    'expr : NOT expr'
    p[0] = UnaryExpr(p[1], p[2], p.lineno(1))


def p_stmt_expr(p):
    '''stmt_expr : assign
                 | method_invocation'''
    p[0] = p[1]


def p_empty(p):
    'empty :'
    p[0] = None


def p_error(p):
    print()
    if p:
        print("Syntax error at token,", p.type, ", line", p.lineno)
    else:
        print("Syntax error at EOF")
    print()
    sys.exit()


def error2(p, i, msg):
    print()
    print(f"Error found while parsing names, line {p.lineno(i)}")
    if msg:
        print(msg)
    print()
    sys.exit()
