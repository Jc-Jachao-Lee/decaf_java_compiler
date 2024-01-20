# Propositional Logic Grammar
import sys
from decaf_absmc import *

# AST Nodes

# gives __str__() access to tables
my_scope = None
my_classes = None

main_found = False
static_fields = 0
recent_loop_type = None

while_counter = 0
for_counter = 0
variable_registers = [[]]


class Node():
    def __init__(self):
        self.parent = None

    def parentCount(self):
        count = 0
        current = self.parent
        while current is not None:
            count += 1
            current = current.parent
        return count


class Program_init(Node):
    def __init__(self, scope, classes):
        global my_scope
        global my_classes

        super().__init__()
        my_scope = scope
        my_classes = classes


# x
class Program(Node):
    def __init__(self, b, scope, classes):
        super().__init__()
        self.body = b
        self.scope = scope
        self.classes = classes

    # to eval we will create a variable child_index = 1
    # as we evaluate nodes, when we encounter a node that creates a scope,
    # move the current name scope to the child_index, then increment child_index by 1

    def __str__(self):
        res = "--------------------------------------------------------------------------\n"
        for node in self.body:
            res += str(node)
        return res

    def code(self):
        global while_counter
        global for_counter
        while_counter = 0
        for_counter = 0
        res = ""

        '''for class_node in self.body:
            # accesses the field of each class body
            for field in class_node.child1.class_parts[0]:
                if field.s_stat:
                    static_fields += 1;
                    new_static((field.f_class, field.name))
                    res += f"# Static field {field.name} from {field.f_class} allocated to offset " \
                           f"{get_static((field.f_class, field.name))}\n"'''

        res += "# Entry point of code.\n"
        res += "call main\n"
        res += "jmp @@exit_reserved_name\n"

        for class_node in self.body:
            res += class_node.code()

        if not main_found:
            res += "# No main function found: generating main label\n"
            res += "main:\nret\n"

        res += "@@exit_reserved_name: \n"

        static_val = f".static_data {static_fields}\n\n"

        return static_val+res


"""
Use An f String to search fields as there can be a variable amount
"""

# variables to count how many methods, vars, and constructors we have seen (only usage is printing)
methods_i = 1
constructors_i = 1
fields_i = 1
vars_i = 1
dynamic_i = 1

# msot recent object on the heap seen
# last_object = 0
calling_object = 0


def error(line, msg):
    print()
    print(f"Error found while parsing names, line {line}")
    if msg:
        print(msg)
    print()
    sys.exit()


def root_class(class_name):
    if class_name == class_name == 'float':
        return 'int'
    if class_name == 'boolean' or class_name == 'int' or class_name == 'string':
        return class_name
    current_class = class_name

    while my_classes[current_class]['parent'] is not None:
        current_class = my_classes[current_class]['parent']

    return current_class


# checks if expr2 is a subtype of expr1
def subtype_match(expr1, expr2):
    class1 = str(expr1.type.val)
    class2 = str(expr2.type.val)

    # primitives
    if class2 == 'int':
        if class1 == 'float' or class1 == 'int':
            return True
        return False

    if class2 == 'boolean' or class2 == 'float' or class2 == 'string':
        if class1 != class2:
            return False
        return True

    # null
    if class2 == 'null':
        if str(expr1.type.t_class) == 'user':
            return True
        else:
            return False

    # constant are a weaker level than the other two, they will generally just take the value
    if str(expr2.type.t_class) != 'constant':
        if str(expr1.type.t_class) != str(expr2.type.t_class):
            return False

    if class2 == class1:
        return True

    else:
        while my_classes[class2]['parent'] is not None:
            class2 = str(my_classes[class2]['parent'])

            if class2 == class1:
                return True

        return False


# t class defines user or class-literal or constant
# error type is " error" to avoid clashes
class TypeNode(Node):
    def __init__(self, var_type, t_class):
        self.val = str(var_type)
        self.t_class = str(t_class)

    def __str__(self):
        if self.t_class == 'constant':
            return self.val
        return f'{self.t_class}({self.val})'


# x
class Class(Node):
    def __init__(self, name):
        super().__init__()
        self.name = name
        self.self_size = 0
        my_classes[name]['class ref'] = self

    def __str__(self):
        res = f"Class name: {self.name}\n"

        parent = my_classes[self.name]['parent']
        if parent is None:
            parent = ""
        res += f"Super Class name: {parent}\n"

        res = res + str(self.child1)

        return res

    def code(self):

        res = "# ------------------------\n"
        res += f"# Beginning of class {self.name}\n"
        res += self.child1.code()
        res += f"# End of class {self.name}\n"
        res += "# ------------------------\n"
        return res


# helps locate variables in our data structure
class DummyNodeField(Node):
    def __init__(self, name, f_class, access1, access2, f_type):
        super().__init__()
        self.name = name
        self.f_class = f_class
        self.s_stat = access1
        self.p_stat = access2

        '''if f_type == 'int' or f_type == 'float' or f_type == 'boolean' or f_type == 'string':
            self.type = TypeNode(f_type, 'user')
        else:
            self.type = TypeNode(f_type, 'user')'''
        if self.s_stat:
            self.type = TypeNode(f_type, 'class_literal')
        else:
            self.type = TypeNode(f_type, 'user')

        global fields_i
        self.field_i = fields_i
        fields_i += 1

        self.scope_index = my_scope[0][-1]

    def __str__(self):

        if self.p_stat:
            privacy_string = 'public'
        else:
            privacy_string = 'private'

        if self.s_stat:
            access_type = 'static'
        else:
            access_type = 'instance'

        return f'FIELD {self.field_i}, {self.name}, {self.f_class}, {privacy_string}, {access_type}, {self.type}\n'

    # allocates a temporary with value, THE CALLER IS RESPONSIBLE FOR SAVING DATA.
    def code(self):
        res = ''
        temp = new_temp_reg()
        self.temp = temp
        res += f"move_immed_i {self.temp}, {self.offset}\n"
        return

    def T(self):
        return self.temp

    def get_offset(self):
        res = ""
        temp = new_temp_reg()
        if self.offset != -5:
            res += f"move_immed_i {temp}, {self.offset}\n"
        else:
            res += f"move {temp}, a0\n"
        return res, temp



class DummyNodeVariable(Node):
    def __init__(self, v_type, name, v_class):
        super().__init__()
        self.name = name
        if v_type == 'int' or v_type == 'float' or v_type == 'boolean' or v_type == 'string':
            self.type = TypeNode(v_type, 'constant')
        else:
            self.type = TypeNode(v_type, 'user')
        self.v_class = v_class
        global vars_i
        self.vars_i = vars_i
        vars_i += 1

        self.scope_index = my_scope[0][-1]

    def __str__(self):
        return f'VARIABLE {self.vars_i}, {self.name}, {self.v_class}, {self.type}\n'

    # ONLY CALLED ON FIRST DECLARATION
    def code(self):
        temp = new_temp_reg()
        variable_registers[-1].append(temp)
        res = ""
        self.temp = temp
        res += f"# register {self.temp} allocated for variable {self.name}\n"
        return res

    def T(self):
        return self.temp


class DummyNodeVariablePointer(Node):
    def __init__(self, variables):
        super().__init__()
        self.vars = variables

    def __str__(self):
        res = ""
        for var in self.vars:
            res += f'{var}, '

        return res[: -2]

    def code(self):
        res = ""
        for var in self.vars:
            res += var.code()
        return res


class DummyExpr(Node):
    def __init__(self, type):
        super().__init__()
        self.type = type


# x
# child1: list of method/constructor nodes
class ClassBody(Node):
    def __init__(self, class_parts):
        super().__init__()
        self.class_parts = class_parts

        # allows children to reference parent if needed
        for part in class_parts:
            for class_item in part:
                class_item.parent = self


    def __str__(self):
        res = ""

        res += "Fields:\n"
        for field in self.class_parts[0]:
            res += str(field)

        res += "Constructors:\n"
        for constructor in self.class_parts[1]:
            res += str(constructor)

        res += "Methods:\n"
        for method in self.class_parts[2]:
            res += str(method)

        return res

    def code(self):
        res = "\n# Fields: \n"
        heap_offset_from_object = 0
        first_static = 1
        # first_dynamic = -1

        for var_ptrs in self.class_parts[0]:
            for field in var_ptrs.vars:
                if field.s_stat:
                    global static_fields
                    static_fields += 1
                    sap_offset = new_static()
                    field.offset = sap_offset

                    res += f"# sap offset {field.offset} given to static field ({field.name}, {field.field_i})\n"
            # not done at class time (done when object created)
                else:
                # val = new_dynamic()
                # if first_dynamic == -1:
                #     first_dynamic = val
                    field.offset = heap_offset_from_object
                    res += f"# offset {heap_offset_from_object} from object given to non static field ({field.name}, {field.field_i})\n"
                    heap_offset_from_object += 1
             
        '''if heap_offset_from_object:   
            res += "# allocate space on heap for object\n"
            temp = new_temp_reg()
            temp2 = new_temp_reg()
            res += f"move_immed_i {temp2} {heap_offset_from_object}\n"
            res += f"halloc {temp}, {temp2}\n"
            destroy_temp(temp)
            destroy_temp(temp2)
            self.base_address = first_dynamic'''
        res += "\n\n# Constructors:\n"
        for constructor in self.class_parts[1]:
            res += constructor.code()

        res += "\n\n# Methods:\n"
        for method in self.class_parts[2]:
            res += method.code()

        return res


# restore = []


# x
class Method(Node):
    # def __init__(self, name, method_class, method_info, formals, scope_index, block):
    def __init__(self, name, method_class, formals, return_type, s_stat, p_stat, scope_index):
        super().__init__()
        # scope index (where our variables will be stored)
        self.scope = scope_index
        self.formals = formals
        for formal in formals:
            formal.parent = self
        self.return_type = return_type
        self.p_stat = p_stat
        self.s_stat = s_stat

        self.name = name
        self.current_class = method_class
        global methods_i
        self.method_i = methods_i
        methods_i += 1

        # self.child1 = block
        # for stmt in block:
        # print(stmt)
        # stmt.parent = self

    def __str__(self):

        # method = self.info

        if self.p_stat:
            privacy_string = 'public'
        else:
            privacy_string = 'private'

        if self.s_stat:
            access_type = 'static'
        else:
            access_type = 'instance'

        res = ""

        res += f"METHOD: {self.method_i}, {self.name}, " \
               f"{self.current_class}, {privacy_string}, {access_type}, {self.return_type}\n"

        formal_str = ""
        for formal in self.formals:
            formal_str += f", {formal.vars_i}"

        # starts at 2 to remove first ", "
        res += f"Method Parameters: {formal_str[2:]}\n"
        res += f"Variable Table: \n"

        def variable_search(index):
            nonlocal res
            if index == 0:
                return

            # print(my_scope[index])

            for key in my_scope[index].keys():
                if key == 'inner scopes':
                    continue

                res += str(my_scope[index][key])

            for i in my_scope[index]['inner scopes']:
                variable_search(i)

        # call it with current scope
        variable_search(self.scope)

        res += f"Method Body:\n{self.child1}"

        # if len(self.child1) != 0:
        #     for node in self.child1:
        #         res += str(node)

        return res

    def code(self):
        global recent_loop_type
        variable_registers.append([])
        saved_loop = recent_loop_type
        recent_loop_type = None
        # restore.append([])

        enter_function()
        res = "\n\n"
        name = f"M_{self.method_i}"
        if self.name == 'main':
            name = 'main'
        res += f"{name}: # label for method\n"
        res += f"# Start of Method: ({self.name}, {self.method_i})\n"
        res += "# Reserving temps for formal variables\n"
        for formal in self.formals:
            formal_code = formal.code()
            #if formal_code[1]:
            #    res += f"save {formal.T()}\n"
            #    restore[-1].append(formal.T())
            res += formal_code
        res += "# Loading initial values for formal variables\n"
        for i, formal in enumerate(self.formals):
            res += f"move {formal.T()} a{i}\n"

        res += "# calling object memory address located in a0\n"
        # res += "# Loading calling object memory address\n"
        # mem_addr = new_temp_reg()
        # res += f"move {mem_addr} a0"

        res += "\n# Method Body:\n"
        res += self.child1.code()

        # destroy_temp(mem_addr)

        if self.name == 'main':
            global main_found
            main_found = 1
            '''registers = restore.pop()
            for register in registers:
                res += f"restore {register}\n"'''
            res += "ret\n"

        res += f"# End of Method: ({self.name}, {self.method_i})\n"
        res += "\n\n"

        leave_function()
        recent_loop_type = saved_loop
        variable_registers.pop()
        return res


# x
# formals [(type, variable name)]
class Constructor(Node):
    # def __init__(self, formals, scope_i, constructor_class, block):
    # def __init__(self, constructor_info, formals, scope_i, block):
    def __init__(self, formals, p_stat, scope_i):
        super().__init__()
        # self.current_class = constructor_class
        self.formals = formals
        # allow variables to reference me
        for node in formals:
            node.parent = self
        # scope
        self.scope = scope_i
        self.p_stat = p_stat

        # self.p = privacy_field
        global constructors_i
        self.constructor_i = constructors_i
        constructors_i += 1

        # self.ttl_children = 1
        # self.child1 = block
        # for stmt in block:
        #    stmt.parent = self

    def __str__(self):

        if self.p_stat:
            privacy_string = 'public'
        else:
            privacy_string = 'private'

        res = ""

        res += f"CONSTRUCTOR: {self.constructor_i}, {privacy_string}\n"

        formal_str = ""
        for formal in self.formals:
            formal_str += f", {formal.vars_i}"
        res += f"Constructor Parameters: {formal_str[2:]}\n"
        res += f"Variable Table: \n"

        def variable_search(index):
            nonlocal res

            for key in my_scope[index].keys():
                if key == 'inner scopes':
                    continue
                res += str(my_scope[index][key])

            for i in my_scope[index]['inner scopes']:
                variable_search(i)

        # call it with current scope
        variable_search(self.scope)

        res += f"Constructor Body:\n{self.child1}"

        # if len(self.child1) != 0:
        #     for node in self.child1:
        #         res += str(node)
        return res

    def code(self):
        global recent_loop_type
        variable_registers.append([])
        saved_loop = recent_loop_type
        recent_loop_type = None
        #restore.append([])

        enter_function()
        res = "\n\n"
        res += f"C_{self.constructor_i}:\n"
        res += f"# Start of Constructor (init function): (CONSTRUCTOR {self.constructor_i})\n"
        res += "# Reserving temps for formal variables\n"
        for formal in self.formals:
            formal_code = formal.code()
            if formal_code[1]:
                res += f"save {formal.T()}\n"
                #restore[-1].append(formal.T())
            res += formal_code[0]
        res += "# Loading initial values for formal variables\n"
        for i, formal in enumerate(self.formals):
            res += f"move {formal.T()} a{i + 1}\n"
        res += "# This object memory address located in a0\n"

        res += "\n# Constructor body: \n"
        res += self.child1.code()

        #registers = restore.pop()
        #for index in range(len(registers), -1, -1):
        #    res += f"restore {registers[index]}\n"
        res += "ret\n"

        res += f"# End of Constructor: (CONSTRUCTOR {self.constructor_i})\n"
        res += "\n\n"
        leave_function()
        recent_loop_type = saved_loop
        variable_registers.pop()
        return res


# x
if_stmt_counter = 0


class IfStmt(Node):
    def __init__(self, condition, then_block, else_block, line):
        super().__init__()
        self.line = line
        global if_stmt_counter
        self.counter = if_stmt_counter
        if_stmt_counter += 1

        self.ttl_children = 2
        self.child1 = condition
        condition.parent = self
        self.child2 = then_block
        then_block.parent = self

        self.child3 = else_block
        else_block.parent = self
        self.ttl_children += 1

        '''if condition.type.val == 'boolean' and then_block.no_type_error and else_block.no_type_error:
            condition.no_type_error = True
        else:
            condition.no_type_error = False'''
        if str(condition.type.val) != 'boolean':
            error(line, "If condition not a boolean")

    def __str__(self):
        return f"If([\n{self.child1},{self.child2},{self.child3}])\n"

    def code(self):
        res = "\n# If statement start\n"
        res += self.child1.code()
        boolean_value = self.child1.T()
        res += f"bz {boolean_value}, false{self.counter}\n"
        res += "# True code\n"
        #print(self.child2)
        res += self.child2.code()
        res += f"jmp if_end{self.counter}\n"
        res += f"false{self.counter}:\n"
        res += self.child3.code()
        res += "# False code\n"
        res += f"if_end{self.counter}:\n"
        res += "# If statement end\n\n"
        if boolean_value not in variable_registers[-1]:
            destroy_temp(boolean_value)
        return res


# x
class ElseStmt(Node):
    def __init__(self, then_block, line):
        super().__init__()
        self.line = line

        self.ttl_children = 1
        self.child1 = then_block
        then_block.parent = self

    def __str__(self):
        return f"Else([\n{self.child1}])\n"

    def code(self):
        return self.child1.code()


# x
# Used for "if without else"
class SkipStmt(Node):
    def __init__(self, line):
        super().__init__()
        self.line = line

    def __str__(self):
        return "\n"

    def code(self):
        return ""


# THIS IS THE ONE EXPRESSION THAT DOES NOT GET A ".T()" FUNCTION. BE CAREFUL
class SkipExpr(Node):
    def __init__(self, line):
        super().__init__()
        self.line = line

    def __str__(self):
        return "{}"

    def code(self):
        return "", 0


# x
class WhileStmt(Node):
    def __init__(self, condition, then_block, line):
        super().__init__()
        global while_counter
        self.line = line
        self.counter = while_counter
        while_counter += 1

        self.ttl_children = 2
        self.child1 = condition
        condition.parent = self
        self.child2 = then_block
        then_block.parent = self

        '''if condition.type.val == 'boolean' and then_block.no_type_error:
            self.no_type_error = True
        else:
            self.no_type_error = False'''
        if str(condition.type.val) != 'boolean':
            error(self.line, "While condition not a boolean")

    def __str__(self):
        return f"WHILE([\n{self.child1},{self.child2}])\n"

    def code(self):
        global recent_loop_type
        recent_loop_type = 'while'
        res = "\n# Start of while statement\n"
        child1_code = self.child1.code()
        res += f"start_while{self.counter}:\n"
        res += child1_code
        boolean_value = self.child1.T()
        res += f"bz {boolean_value} end_while{self.counter}\n"
        res += self.child2.code()
        res += f"jmp start_while{self.counter}\n"
        res += f"end_while{self.counter}:\n"
        if boolean_value not in variable_registers[-1]:
            destroy_temp(boolean_value)
        res += "\n# End of while statement\n"
        recent_loop_type = None


        return res


# x
class ForStmt(Node):
    def __init__(self, initializer, condition, update, then_block, line):
        super().__init__()
        self.line = line

        self.ttl_children = 4
        self.child1 = condition
        condition.parent = self
        self.child2 = then_block
        then_block.parent = self
        self.child3 = initializer
        initializer.parent = self
        # self.tll_children += 1
        self.child4 = update
        update.parent = self
        # self.tll_children += 1

        '''if condition.type.val == 'boolean' and initializer.no_type_error and update.no_type_error and then_block.no_type_error:
            self.no_type_error = True
        else:
            self.no_type_error = False'''
        if str(condition.type.val) != 'boolean':
            error(self.line, "For statement condition not a boolean")

    def __str__(self):
        return f"FOR([\n{self.child3},{self.child1},{self.child4},{self.child2}])\n"

    def code(self):
        global recent_loop_type
        global for_counter
        self.counter = for_counter
        for_counter += 1
        recent_loop_type = 'for'
        registers_to_save = []
        res = "\n# Start of for loop\n"
        # init
        if isinstance(self.child3, SkipExpr):
            temp3 = ""
        else:
            temp3 = self.child3.code()
            registers_to_save.append((self.child3.T()))
        # condition
        temp1 = self.child1.code()
        boolean_value = self.child1.T()
        registers_to_save.append((self.child1.T()))
        # update
        if isinstance(self.child4, SkipExpr):
            temp4 = ""
        else:
            temp4 = self.child4.code()
            registers_to_save.append((self.child4.T()))

        # initalizer
        res += "# initializer\n"
        res += temp3
        res += f"start_for{self.counter}:\n"
        # condition
        res += "# condition\n"
        res += temp1
        res += f"bz {boolean_value} end_for{self.counter}\n"

        # update
        res += "# update\n"
        res += temp4

        # code body
        res += "# for body\n"
        res += self.child2.code()

        res += f"jmp start_for{self.counter}\n"
        res += f"end_for{self.counter}:\n"

        res += "# End of for loop\n\n"
        recent_loop_type = None
        for register in registers_to_save:
            if register not in variable_registers[-1]:
                destroy_temp(register)

        return res


# x
class ReturnStmt(Node):
    def __init__(self, type_to_match, value, function_node, line):
        super().__init__()
        self.line = line

        if value is None:
            self.ttl_children = 0
        else:
            self.ttl_children = 1
            self.child1 = value
            value.parent = self

        if type_to_match == 'void':
            if value is None:
                # self.no_type_error = True
                pass
            else:
                # self.no_type_error = False
                error(line, f"found value of type {value.type.val}, void expected")
        else:
            temp_type = TypeNode(type_to_match, value.type.t_class)
            temp_expr = DummyExpr(temp_type)
            if subtype_match(temp_expr, value):
                # self.no_type_error = True
                pass
            else:
                # self.no_type_error = False
                error(line, f"found value of type {value.type.val}, {type_to_match} expected")

        self.r_class = function_node.current_class
        function_node.return_node = self

    def __str__(self):
        if self.ttl_children:
            return f"RETURN ({self.child1})\n"
        return f"RETURN ()\n"

    def code(self):
        res = "# Return statement start\n"
        # res += "# Restoring temp registers that were used\n"
        # registers = restore.pop()
        # for index in range(len(registers), -1, -1):
        #     res += f"restore {registers[index]}\n"

        # loading a variable
        res += self.child1.code()
        if self.ttl_children != 0:
            res += f"move a0, {self.child1.T()}\n"
        res += 'ret\n'
        res += "# Return statement end\n"

        return res

    def get(self):
        # global dynamic_i
        # object_id = dynamic_i
        # dynamic_i += 1

        fields = my_classes[self.r_class]['fields']
        total_allocated = 0

        base_addr = None
        for field_name, field in fields.items():
            if not field.s_stat:
                val = new_dynamic()
                total_allocated += 1
                if base_addr is None:
                    base_addr = val
        # offsets[object_id] = base_addr
        return base_addr
# x
# invoked after a valid expression is verified
class ExpressionStmt(Node):
    def __init__(self, expr, line):
        super().__init__()
        self.line = line

        self.ttl_children = 1
        self.child1 = expr
        expr.parent = self

        if str(expr.type.val) != ' error':
            # self.no_type_error = True
            pass
        else:
            # self.no_type_error = False
            error(line, "expression has type error")

    def __str__(self):
        return f"ExprStmt([{self.child1}])\n"

    def code(self):
        return self.child1.code()


# x
class BlockStmt(Node):
    def __init__(self, stmts, line):
        super().__init__()
        self.line = line

        self.ttl_children = 1
        self.child1 = stmts

        '''self.no_type_error = True
        for stmt in stmts:
            stmt.parent = self
            self.no_type_error = self.no_type_error and stmt.no_type_error'''

    def __str__(self):
        res = ""
        for stmt in self.child1:
            res += str(stmt) + ", "
        return f"Block([\n{res[:-2]}])\n"

    def code(self):
        res = "# BLOCK START\n"
        for stmt in self.child1:
            res += stmt.code()
        res += "# BLOCK END\n"
        return res


# x
class BreakStmt(Node):
    def __init__(self, line):
        super().__init__()
        self.line = line

    def __str__(self):
        return f"Break()\n"

    def code(self):
        if recent_loop_type is None:
            return ""
        elif recent_loop_type == 'while':
            return f"jmp end_while{self.counter}:\n"
        elif recent_loop_type == 'for':
            return f"jmp end_for{self.counter}\n"
        else:
            return ""


# x
class ContinueStmt(Node):
    def __init__(self, line):
        super().__init__()
        self.line = line

    def __str__(self):
        return f"Continue([])"

    def code(self):
        if recent_loop_type is None:
            return ""
        elif recent_loop_type == 'while':
            return f"jmp start_while{self.counter}:\n"
        elif recent_loop_type == 'for':
            return f"jmp start_for{self.counter}\n"
        else:
            return ""


# x
class IntegerConstantExpr(Node):
    def __init__(self, value, line):
        super().__init__()
        self.line = line
        self.value = int(value)
        self.type = TypeNode('int', 'constant')

    def __str__(self):
        return f"Constant(Integer-constant({self.value}))"

    def code(self):
        res = ""
        temp = new_temp_reg()

        self.temp = temp
        res += f'move_immed_i {self.temp}, {self.value}\n'
        return res

    def T(self):
        return self.temp


# x
class FloatConstantExpr(Node):
    def __init__(self, value, line):
        super().__init__()
        self.line = line
        self.value = float(value)
        self.type = TypeNode('float', 'constant')

    def __str__(self):
        return f"Constant(Float-constant({self.value}))"

    def code(self):
        res = ""
        temp = new_temp_reg()
        self.temp = temp
        res += f'move_immed_f {self.temp}, {self.value}\n'
        return res

    def T(self):
        return self.temp


# there are no strings!
class StringConstantExpr(Node):
    def __init__(self, value, line):
        super().__init__()
        self.line = line
        self.value = value
        self.type = TypeNode('string', 'constant')

    def __str__(self):
        return f"Constant(Float-constant({self.value}))"


# x
class NullConstantExpr(Node):
    def __init__(self, line):
        super().__init__()
        self.line = line
        self.value = None
        self.type = TypeNode('null', 'constant')
        self.offset = -1

    def __str__(self):
        return f"Constant(Null-constant(None))"

    def code(self):
        res = ""
        res += "# Suppose 0 is used as the value for null in decaf absmc\n"
        temp = new_temp_reg()
        self.temp = temp
        res += f'move_immed_i {self.temp}, 0\n'
        return res

    def T(self):
        return self.temp

    def get_offset(self):
        res = ""
        temp = new_temp_reg()
        if self.offset != -5:
            res += f"move_immed_i {temp}, {self.offset}\n"
        else:
            res += f"move {temp}, a0\n"
        return res, temp





# x
class BooleanConstantExpr_True(Node):
    def __init__(self, line):
        super().__init__()
        self.line = line
        self.value = True
        self.type = TypeNode('boolean', 'constant')

    def __str__(self):
        return f"Constant(Boolean-constant({self.value}))"

    def code(self):
        res = ""
        res += "# Suppose 1 is used as the value for true in decaf_absmc\n"
        temp = new_temp_reg()
        self.temp = temp
        res += f'move_immed_i {self.temp}, 1\n'
        return res

    def T(self):
        return self.temp


# x
class BooleanConstantExpr_False(Node):
    def __init__(self, line):
        super().__init__()
        self.line = line
        self.value = False
        self.type = TypeNode('boolean', 'constant')

    def __str__(self):
        return f"Constant(Boolean-constant({self.value}))"

    def code(self):
        res = ""
        res += "# Suppose 0 is used as the value for false in decaf_absmc\n"
        temp = new_temp_reg()
        self.temp = temp
        res += f'move_immed_i {self.temp}, 0\n'
        return res

    def T(self):
        return self.temp


# x
# Used as a pointer to the variable list to get information about the variable
class VariableExpr(Node):
    def __init__(self, val_node, line):
        super().__init__()
        self.line = line
        self.node = val_node
        self.type = val_node.type

    def __str__(self):
        return f"Variable({self.node.name})"

    # im pretty sure this wants no code
    def code(self):
        if self.node in variable_offset_finder:
            self.offset = variable_offset_finder[self.node]
        return ""

    def T(self):
        return self.node.T()

    def get_offset(self):
        res = ""
        temp = new_temp_reg()
        if self.offset != -5:
            res += f"move_immed_i {temp}, {self.offset}\n"
        else:
            res += f"move {temp}, a0\n"
        return res, temp



# x
class UnaryExpr(Node):
    def __init__(self, operator, operand, line):
        super().__init__()
        self.line = line
        self.operator = operator

        self.ttl_children = 1
        self.child1 = operand
        operand.parent = self

        if operator == '!':
            if str(self.child1.type.val) == 'boolean':
                self.type = TypeNode('boolean', 'constant')
            else:
                # error
                error(line, f"boolean expected, {self.child1.type} received")
        else:
            if str(self.child1.type.val) == 'float' or str(self.child1.type) == 'int':
                self.type = TypeNode(self.child1.type.val, 'constant')
            else:
                self.type = TypeNode(' error', 'constant')
                error(line, f"float or int expected, {self.child1.type} received")

    def __str__(self):
        return f"Unary({self.operator}, {self.child1})"

    def code(self):
        res = "# Begin Unary Expression\n"
        res += self.child1.code()

        temp2 = new_temp_reg()

        self.temp = temp2
        res += f'move_immed_i {self.temp}, 0\n'

        if self.operator == '!':
            res += f'fleq {self.temp} {self.child1.T()} {self.temp}\n'
        elif self.operator == '-':
            if str(self.type.val) == 'int':
                res += f'isub {self.temp}, {self.temp}, {self.child1.T()}\n'
            else:
                res += f'fsub {self.temp}, {self.temp}, {self.child1.T()}\n'
        elif self.operator == '+':
            if str(self.type.val) == 'int':
                res += f'iadd {self.temp}, {self.temp}, {self.child1.T()}\n'
            else:
                res += f'fadd {self.temp}, {self.temp}, {self.child1.T()}\n'
        else:
            pass

        if self.child1.T() not in variable_registers[-1]:
            destroy_temp(self.child1.T())

        res += "# End Unary Expression\n"

        return res

    def T(self):
        return self.temp


# x
class BinaryExpr(Node):
    def __init__(self, operand1, operand2, operator, line):
        super().__init__()
        self.line = line
        self.operator = operator

        self.ttl_children = 2
        self.operand1 = operand1
        operand1.parent = self
        self.operand2 = operand2
        operand2.parent = self

        # arithmetic operator
        current_type = "SHOULD NEVER APPEAR"
        if str(operand1.type.val) == ' error' or str(operand2.type.val) == ' error':
            current_type = ' error'
            error(line, f"lhs or rhs has type error")

        elif operator == 'add' or operator == 'sub' or operator == 'mult' or operator == 'div':
            current_type = 'int'
            if str(operand1.type.val) == 'float':
                current_type = 'float'
            elif str(operand1.type.val) != 'int':
                current_type = ' error'
                error(line, f"Int or float expected")

            if str(operand2.type.val) == 'float':
                current_type = 'float'
            elif str(operand2.type.val) != 'int':
                current_type = ' error'
                error(line, f"Int or float expected")

        # arithmetic comparison
        elif operator == 'lt' or operator == 'lte' or operator == 'gt' or operator == 'gte':
            if (str(operand1.type.val) == 'float' or str(operand1.type.val) == 'int') and (
                    str(operand2.type.val) == 'float' or str(operand2.type.val) == 'int'):
                current_type = 'boolean'
            else:
                current_type = ' error'
                error(line, f"Expected numerical types in both operand1 and operand2")

        # logical operation
        elif operator == 'or' or operator == 'and':
            if str(operand1.type.val )== 'boolean' and str(operand2.type.val) == 'boolean':
                current_type = 'boolean'
            else:
                current_type = ' error'
                error(line, f"BinaryExpr")

        # equality comparison
        elif operator == 'eq' or 'neq':
            if str(operand1.type.val) == 'null':
                if operand2.type.t_class == 'user':
                    current_type = 'boolean'
                else:
                    current_type = ' error'
                    error(line, f"BinaryExpr incompatible types (null + non user)")
            elif str(operand2.type.val) == 'null':
                if operand1.type.t_class == 'user':
                    current_type = 'boolean'
                else:
                    current_type = ' error'
                    error(line, f"BinaryExpr incompatible types (null + non user)")
            else:
                if (str(operand1.type.t_class) == str(operand2.type.t_class)) or \
                        str(operand2.type.t_class) == 'constant':
                    if root_class(str(operand1.type.val)) == root_class(str(operand2.type.val)):
                        current_type = 'boolean'
                    else:
                        current_type = ' error'
                        error(line, f"BinaryExpr")
                else:
                    # print("here?")
                    current_type = ' error'
                    error(line, f"BinaryExpr, {operand1.type.t_class} does not match {operand2.type.t_class}")
            pass

        else:
            current_type = ' error'
            error(line, f"BinaryExpr")

        self.type = TypeNode(current_type, 'constant')

    def __str__(self):
        return f"Binary({self.operator}, {self.operand1}, {self.operand2})"

    def code(self):
        res = "# Begin Binary Expression\n"
        temp = new_temp_reg()
        self.temp = temp

        res += self.operand1.code()
        res += self.operand2.code()
        op1 = self.operand1.T()
        op2 = self.operand2.T()

        temp2 = new_temp_reg()

        if self.operator == 'add':
            res += "# Add\n"
            if str(self.type.val) == 'float':
                res += f"fadd {self.temp}, {op1}, {op2}\n"
            else:
                res += f"iadd {self.temp}, {op1}, {op2}\n"
        elif self.operator == 'sub':
            res += "# Sub\n"
            if str(self.type.val) == 'float':
                res += f"fsub {self.temp}, {op1}, {op2}\n"
            else:
                res += f"isub {self.temp}, {op1}, {op2}\n"
        elif self.operator == 'mult':
            res += "# Mult\n"
            if str(self.type.val) == 'float':
                res += f"fmul {self.temp}, {op1}, {op2}\n"
            else:
                res += f"imul {self.temp}, {op1}, {op2}\n"
        elif self.operator == 'div':
            res += "# Div\n"
            if str(self.type.val) == 'float':
                res += f"fdiv {self.temp}, {op1}, {op2}\n"
            else:
                res += f"idiv {self.temp}, {op1}, {op2}\n"
        elif self.operator == 'and':
            res += "# and\n"
            res += f"move_immed_i {self.temp} 2\n"
            res += f"isub {self.temp}, {self.temp}, {op2}\n"
            res += f"isub {self.temp}, {self.temp}, {op1}\n"
            res += f"ilt {self.temp}, {self.temp} {op1} # either boolean work as second argument\n"

        elif self.operator == 'or':
            res += "# or\n"
            res += f"move_immed_i {self.temp} 0\n"
            res += f"move_immed_i {self.temp} 1\n"
            res += f"iadd {self.temp}, {self.temp}, {op2}\n"
            res += f"iadd {self.temp}, {self.temp}, {op1}\n"
            res += f"igte {self.temp}, {self.temp} {temp2}\n"

        elif self.operator == 'eq':
            res += "# eq\n"
            if str(self.type.val) == 'float':
                res += f"fsub {self.temp}, {op1}, {op2}\n"
                res += f"move_immed_f {temp2} 0\n"
                res += f"fleq {self.temp} {self.temp} {temp2}\n"
            else:
                res += f"isub {self.temp}, {op1}, {op2}\n"
                res += f"move_immed_i {temp2} 0\n"
                res += f"ileq {self.temp} {self.temp} {temp2}\n"

        elif self.operator == 'neq':
            res += "# neq\n"
            if str(self.type.val) == 'float':
                res += f"fsub {self.temp}, {op1}, {op2}\n"
                res += f"move_immed_f {temp2} 0\n"
                res += f"fleq {self.temp} {self.temp} {temp2}\n"
                res += f'fleq {self.temp} {temp2} {self.temp} # reverses the bit\n'
            else:
                res += f"isub {self.temp}, {op1}, {op2}\n"
                res += f"move_immed_i {temp2} 0\n"
                res += f"ileq {self.temp} {self.temp} {temp2}\n"
                res += f'ileq {self.temp} {temp2} {self.temp} # reverses the bit\n'

        elif self.operator == 'lt':
            res += "# lt\n"
            if str(self.type.val) == 'float':
                res += f"flt {self.temp}, {op1}, {op2}\n"
            else:
                res += f"ilt {self.temp}, {op1}, {op2}\n"

        elif self.operator == 'lte':
            res += "# lte\n"
            if str(self.type.val) == 'float':
                res += f"fleq {self.temp}, {op1}, {op2}\n"
            else:
                res += f"ileq {self.temp}, {op1}, {op2}\n"

        elif self.operator == 'gt':
            res += "# gt\n"
            if str(self.type.val) == 'float':
                res += f"fgt {self.temp}, {op1}, {op2}\n"
            else:
                res += f"fgt {self.temp}, {op1}, {op2}\n"

        elif self.operator == 'gte':
            res += "# gte\n"
            if str(self.type.val) == 'float':
                res += f"fgeq {self.temp}, {op1}, {op2}\n"
            else:
                res += f"fgeq {self.temp}, {op1}, {op2}\n"

        if str(op1) not in variable_registers[-1]:
            destroy_temp(op1)
            # print(f"variable registers: {variable_registers}")
            # print(f"{op1} destroyed")
        if str(op2) not in variable_registers[-1]:
            destroy_temp(op2)
            # print(f"variable registers: {variable_registers}")
            # print(f"{op2} destroyed")

        destroy_temp(temp2)
        res += "# End Binary Expression\n"
        return res

    def T(self):
        return self.temp


# x
class AssignExpr(Node):
    def __init__(self, lhs, rhs, line):
        super().__init__()
        self.line = line

        self.ttl_children = 2
        self.child1 = lhs
        lhs.parent = self
        self.child2 = rhs
        rhs.parent = self

        if str(lhs.type.val) == ' error' or str(rhs.type.val) == ' error':
            self.type = TypeNode(' error', 'constant')
            error(line, f"AssignExpr, lhs/rhs had a type error")
        else:
            if subtype_match(lhs, rhs):
                if str(rhs.type.val) == 'int' or str(rhs.type.val) == 'float' or str(rhs.type.val) == 'boolean':
                    self.type = TypeNode(rhs.type.val, 'constant')
                else:
                    self.type = TypeNode(rhs.type.val, 'user')
            else:
                self.type = TypeNode(' error', 'constant')
                error(line, f"AssignExpr, subtype mismatch: {lhs.type}, "f"{rhs.type}")

    def __str__(self):
        return f"Assign({self.child1}, {self.child2}, {self.child1.type}, {self.child2.type})"

    def code(self):
        res = ""

        res += "# Begin assignment:\n"
        # rhs has the value we are looking for
        res += self.child1.code()
        res += self.child2.code()


        # print(f"ASSIGNMENT TYPE CLASS {self.child1.type.t_class} = {self.child2.type.t_class}")

        if self.child1.type.t_class == 'user':
            #print("This is true")

            rhs_type = self.child2.type.val
            if str(rhs_type) != 'float' and str(rhs_type) != 'int' and str(rhs_type) != 'boolean':
                if hasattr(self.child2, 'offset'):
                    if isinstance(self.child1, VariableExpr):
                        # print("an offset was given")
                        variable_offset_finder[self.child1.node] = self.child2.offset

                    if isinstance(self.child1, FieldAccessExpr):
                        # print("an offset was given")
                        variable_offset_finder[self.child1.field] = self.child2.offset
                else:
                    error(self.line, "err: offset not found, heap")

        if self.child1.type.t_class == 'class_literal':
            rhs_type = self.child2.type.val
            if str(rhs_type) != 'float' and str(rhs_type) != 'int' and str(rhs_type) != 'boolean':
                if hasattr(self.child2, 'offset'):
                    if isinstance(self.child1, FieldAccessExpr):
                        variable_offset_finder[self.child1.field] = self.child2.offset
                else:
                    error(self.line, "err: offset not found, sap")

        lhsreg = self.child1.T()
        rhsreg = self.child2.T()
        reg3 = new_temp_reg()


        '''if self.child2.type.t_class == 'user':
            res += f'move_immed_i {reg4} 0\n'
            res += f"hload {reg3} {rhsreg} {reg4}   # we need to retrieve the value to load\n"

        elif self.child2.type.t_class == 'class_literal':
            res += f"hload {reg3} sap {rhsreg}   # we need to retrieve the value to load\n"
        else:
            res += f"move {reg3} {rhsreg}    # we need to retrieve the value to load\n"'''

        if self.child1.type.t_class == 'user':
            res += f'move_immed_i {reg3} 0\n'
            res += f'hstore {lhsreg}, {reg3}, {rhsreg}\n'
            res += f'move {reg3} {rhsreg}\n'
            self.temp = reg3
        elif self.child1.type.t_class == 'class_literal':
            res += f'hstore sap, {lhsreg}, {rhsreg}\n'
            res += f'move {reg3} {rhsreg}\n'
            self.temp = reg3
        else:
            res += f'move {lhsreg} {rhsreg}\n'
            self.temp = lhsreg
            destroy_temp(reg3)

        if rhsreg not in variable_registers[-1]:
            destroy_temp(rhsreg)

        res += "# End assignment\n"
        return res

    def T(self):
        return self.temp


# X
# operation: '++' or '--'
# post_or_pre: Post or Pre
class AutoExpr(Node):
    def __init__(self, operand, operation, post_or_pre, line):
        super().__init__()
        self.line = line
        self.operation = operation
        self.type = post_or_pre

        self.ttl_children = 1
        self.operand = operand
        operand.parent = self

        if str(operand.type.val) == 'int' or str(operand.type.val) == 'float':
            self.type = TypeNode(operand.type.val, "constant")
        else:
            self.type = TypeNode(' error', "constant")
            error(line, f"AutoExpr")

    def __str__(self):
        return f"Auto({self.operation}, {self.type}, {self.operand})"

    def code(self):
        temp = new_temp_reg()
        temp_maybe = None
        temp_2 = None
        res = "# Start of auto expr: \n"
        res += self.operand.code()
        self.temp = self.operand.T()
        res += f"move_immed_i {temp}, 1\n"
        if self.operation == '++':
            if str(self.operand.type.val) == 'float':
                res += f"ftoi {temp} {temp}\n"
                res += f"fadd {self.temp} {temp} {self.temp}\n"
            else:
                res += f"iadd {self.temp} {temp} {self.temp}\n"
        else:
            if str(self.operand.type.val) == 'float':
                res += f"ftoi {temp} {temp}\n"
                res += f"fsub {self.temp} {self.temp} {temp}\n"
            else:
                res += f"isub {self.temp} {self.temp} {temp}\n"

        if self.operand.type.t_class == 'user':
            # base_offset = offsets[last_object]
            #if self.operand in variable_offset_finder:
            #    offset = variable_offset_finder[self.operand]
            if hasattr(self.operand, 'offset'):
                offset, temp_maybe = self.operand.get_offset()
                res += offset
                # offset = self.operand.offset
            else:
                # print(self.line, f"No object to find: {self.operand}")
                pass

            if isinstance(self.operand, FieldAccessExpr):
                a, temp_2 = self.operand.field.get_offset()
                res += a
                res += f'move {temp} {temp_2}\n'
                res += f'hstore {temp_maybe}, {temp}, {self.temp}\n'
            else:
                # print("Some text that happens in autoexpr (dynamic section)")
                pass
        elif self.operand.type.t_class == 'class_literal':
            if isinstance(self.operand, FieldAccessExpr):
                a, temp_2 = self.operand.field.get_offset()
                res += a
                res += f'move {temp} {temp_2}\n'
                res += f'hstore sap, {temp}, {self.temp}\n'
            else:
                # print("Some text that happens in autoexpr (static section)")
                pass

        destroy_temp(temp)
        if temp_maybe is not None:
            destroy_temp(temp_maybe)
        if temp_2 is not None:
            destroy_temp(temp_2)

        res += "# End of auto expr\n"

        return res

    def T(self):
        return self.temp


# x
class FieldAccessExpr(Node):
    def __init__(self, base, field_name, current_class, line):
        super().__init__()
        self.line = line

        self.base = base
        base.parent = self
        # extra size needed from where it normally is due to being resolved recursively through the parent
        self.extra_size = 0

        def find_field():
            class_counter = base.type.val
            while True:
                for key, item in my_classes[class_counter]['fields'].items():
                    if str(field_name) == str(key):
                        # found field but we do not have access. We know we will not find the field in this class.
                        if item.p_stat == 0 and str(class_counter) != str(current_class):
                            break
                        else:
                            return item
                if my_classes[class_counter]['parent'] is None:
                    break
                self.extra_size += my_classes[class_counter]['class ref'].self_size
                class_counter = my_classes[class_counter]['parent']
            return False

        field = find_field()
        if field:

            self.field = field
            self.field.parent = self

            #print(field)

            # only one field of a specific name could exist
            if self.field.s_stat:
                if base.type.t_class != 'class_literal':
                    self.type = TypeNode(' error', "constant")
                    error(line, f"FieldAccessExpr, static field invoked by non class literal")
            else:
                if base.type.t_class != 'user':
                    self.type = TypeNode(' error', "constant")
                    error(line, f"FieldAccessExpr, non static field invoked by class literal")
            '''if field.type.val == 'int' or field.type.val == 'boolean' or field.type.val == 'float' or field.type.val == 'string':
                self.type = TypeNode(field.type.val, "user")
            else:'''
            self.type = TypeNode(field.type.val, base.type.t_class)
        else:
            self.type = TypeNode(' error', "constant")
            error(line, f"FieldAccessExpr, no field found")

    def __str__(self):
        val = "No Field Resolved"
        if str(self.type.val) != ' error':
            val = self.field.field_i
        return f"Field-access({self.field.name}, {self.base}, {val})"

    def code(self):
        # self.base.code()

        res = f"# Start field access ({self.field.name},{self.field.field_i}):\n"

        res += self.base.code()

        temp1 = new_temp_reg()
        temp2 = new_temp_reg()
        text, temp3 = self.field.get_offset()
        res += text
        if self.field.s_stat:
            # val = self.field.offset
            res += f"move {temp1}, {temp3}\n"
            res += f"move_immed_i {temp2}, {0}\n"
            res += f"hload {temp1}, {temp1}, {temp2}\n"
        else:
            # if not hasattr(self.base.node, 'object_id'):
            #     error(self.line, "uninitialized field access")
            # global last_object
            # last_object = self.base.node.object_id
            # object_offset = offsets[self.base.node.object_id]
            if self.base in variable_offset_finder:
                if variable_offset_finder[self.base] != -5:
                    offset = variable_offset_finder[self.base] + self.extra_size
                    self.offset = offset + self.field.offset
                else:
                    self.offset = -5
            elif hasattr(self.base, 'offset'):

                if self.base.offset != -5:
                    offset = self.base.offset + self.extra_size
                    self.offset = offset + self.field.offset
                else:
                    self.offset = -5
            else:
                # print(self.line, "No object to find")
                pass

            res += f"# In the case of a 'primitive' value, this loads the object. Otherwise it loads memory location.\n"
            res += f"move {temp1}, {temp3}\n"
            res += f"move {temp2}, {temp3}\n"
            res += f"hload {temp1}, {temp1}, {temp2}\n"

            '''field_type = self.field.type.val
            if str(field_type) != 'int' and str(field_type) != 'boolean' and str(field_type) != 'float':
                res += "# move to the heap location shown by the value of the field pointer\n"
                temp3 = new_temp_reg()
                res += f"move_immed_i {temp2}, {0}\n"
                res += f"hload {temp1}, {temp1}, {temp2}\n"'''

        self.temp = temp1
        destroy_temp(temp2)
        if temp3 is not None:
            destroy_temp(temp3)

        res += f"# End field access ({self.field.name},{self.field.field_i})\n"
        return res

    # returns temp with offset to find field in heap
    def T(self):
        return self.temp

    def get_offset(self):
        res = ""
        temp = new_temp_reg()
        if self.offset != -5:
            res += f"move_immed_i {temp}, {self.offset}\n"
        else:
            res += f"move {temp}, a0\n"
        return res, temp

# x
class MethodCallExpr(Node):
    def __init__(self, base, method_name, arguments, current_class, line):
        super().__init__()
        self.line = line
        self.method_name = method_name

        self.child1 = base
        base.parent = self

        if arguments is not None:
            self.child2 = arguments
            for argument in arguments:
                argument.parent = self
        else:
            self.child2 = []

        def find_method():
            class_counter = self.child1.type.val
            while True:
                for method_name in my_classes[class_counter]['methods'].keys():
                    # print(method_name)
                    if method_name != self.method_name:
                        continue

                    methods = my_classes[class_counter]['methods'][method_name]
                    for i in range(len(methods)):
                        formals = methods[i].formals
                        # print(formals)

                        # different amount of arguments / paramaeters
                        if len(formals) != len(self.child2):
                            continue

                        # 0 p_stat means private
                        if methods[i].p_stat == 0 and current_class != class_counter:
                            continue

                        found = True
                        for i, formal in enumerate(formals):
                            if not subtype_match(formal, self.child2[i]):
                                return None, 2

                        if found:
                            return methods[i], -1
                if my_classes[class_counter]['parent'] is None:
                    break
                class_counter = my_classes[class_counter]['parent']

            return None, 1

        method_found, method_found_class = find_method()
        if method_found:
            self.method = method_found
            if (method_found.s_stat and base.type.t_class == 'class_literal') or (
                    not method_found.s_stat and base.type.t_class == 'user'):
                if method_found.return_type == 'int' or method_found.return_type == 'float' or method_found.return_type == 'boolean' or method_found.return_type == 'string':
                    self.type = TypeNode(method_found.return_type, 'constant')
                else:
                    self.type = TypeNode(method_found.return_type, 'user')
            else:
                self.type = TypeNode(' error', 'constant')
                error(line, f"Invalid access")
        else:
            self.type = TypeNode(' error', 'constant')
            if method_found_class == 1:
                error(line, f"Method not found: {method_name}")
            elif method_found_class == 2:
                error(line, f"Method not found: {method_name}, parameter type mismatch")

    def __str__(self):
        if str(self.type.val) == ' error':
            value = 'No Method Resolved'
        else:
            value = self.method.method_i
        res = f"Method-call({str(self.method_name)}, {self.child1}, {value}, ["
        for argument in self.child2:
            res += f"{str(argument)}, "
        return res[:-2] + "])"

    def code(self):
        # global last_object
        # global calling_object
        if self.child1.type.t_class == 'user' or self.child1.type.t_class == 'class_literal':
            type = self.method.return_type
            self.offset = self.method.return_node.get()
            global calling_object
            calling_object = self.offset
            # self.object_id = last_object
            # calling_object = self.offset
            # print("we recieve an object id")

        # if(last_object == -1):
        #    print("OOPS")

        res = "# Start method call expr:\n"
        temp = new_temp_reg()
        self.temp = temp

        res += f"save a0\n"
        if self.offset is not None:
            res += f"move a0, {self.offset} # pass in the offset of the calling object as the first parameter\n"
        else:
            res += f"move a0, -1 # place holder value as the object has no dynamically allocated fields\n" \
                   f"            # this value has no usage\n"
        amount = 1
        for argument in self.child2:
            res += f"save a{amount}\n"
            res += argument.code()
            res += f"move a{amount} {argument.T()}\n"
            if argument.T() not in variable_registers[-1]:
                destroy_temp(argument.T())
            amount += 1

        reg_list = []
        for register in range(temp_reg_size[-1]):
            # check if temp register is in use
            register = f"t{register}"
            if register not in temp_registers[-1]:
                res += f"save {register}\n"
                reg_list.append(register)

        res += f"call M_{self.method.method_i}\n"

        for register in reg_list:
            res += f"restore {register}\n"

        for index in range(len(self.child2), 0, -1):
            res += f"restore a{index}\n"

        res += f"move {temp} a0\n"
        res += f"restore a0\n"

        res += "# End method call expr\n"

        return res

    def T(self):
        return self.temp

    def get_offset(self):
        res = ""
        temp = new_temp_reg()
        if self.offset != -5:
            res += f"move_immed_i {temp}, {self.offset}\n"
        else:
            res += f"move {temp}, a0\n"
        return res, temp


# x
class NewObjectExpr(Node):
    def __init__(self, class_name, constructor_args, current_class, line):
        super().__init__()
        self.line = line
        self.class_name = class_name

        if constructor_args is not None:
            self.child1 = constructor_args
            for constructor_arg in constructor_args:
                constructor_arg.parent = self
        else:
            self.child1 = []

        # name resolution
        obj_id = -1
        for _, constructor_node in my_classes[class_name]['constructors'].items():
            if current_class != class_name and constructor_node.p_stat == 0:
                continue

            formal_parameters = constructor_node.formals
            # param/arg count do not match
            if len(formal_parameters) != len(constructor_args):
                continue

            found = True
            for i, formal in enumerate(formal_parameters):
                if not subtype_match(formal, constructor_args[i]):
                    found = False
                    break

                # closest match possible
                if obj_id != -1 and subtype_match(constructor_args[obj_id], constructor_args[i]):
                    found = False
                    break

            if found:
                obj_id = constructor_node.constructor_i

        if obj_id != -1:
            self.type = TypeNode(class_name, 'user')
            self.constructor_invoked = obj_id
        else:
            self.type = TypeNode(' error', 'constant')
            error(line, f"No Object found")

        # global dynamic_i
        # self.object_id = dynamic_i
        # dynamic_i += 1

    def __str__(self):
        val = 'No Constructor Resolved'
        if self.constructor_invoked != -1:
            val = self.constructor_invoked

        res = f"New-object({self.class_name}, {val}, ["
        for argument in self.child1:
            res += f"{str(argument)}, "
        return res[:-2] + "])"

    def code(self):
        # global last_object
        # last_object = self.object_id

        res = ""
        self.offset = None
        size = my_classes[self.class_name]['class ref'].size
        # total_allocated = 0

        for i in range(size):
            val = new_dynamic()
            # total_allocated += 1
            if self.offset is None:
                self.offset = val
                global calling_object
                calling_object = self.offset

        '''for field_name, field in fields.items():
            if not field.s_stat:
                val = new_dynamic()
                total_allocated += 1
                if self.offset is None:
                    self.offset = val
                    global calling_object
                    calling_object = self.offset'''
        # offsets[self.object_id] = self.base_addr
        temp = new_temp_reg()
        #if overwrite:
        #    res += f'save {temp}\n'
        #   restore[-1].append(temp)

        temp2 = new_temp_reg()
        #if overwrite:
        #    res += f'save {temp2}\n'
        #    restore[-1].append(temp2)

        self.temp = temp

        res += "# Start of new object expr:\n"
        res += f"move_immed_i {temp}, {val}\n"
        res += f"move_immed_i {temp2}, {size}\n"
        res += f"halloc {temp}, {temp2}\n"
        destroy_temp(temp2)

        res += f"save a0\n"
        res += f"move a0, {temp}\n"
        amount = 1
        for argument in self.child1:
            res += f"save a{amount}\n"
            res += argument.code()
            res += f"move a{amount} {argument.T()}\n"
            if argument.T not in variable_registers[-1]:
                destroy_temp(argument.T())
            amount += 1

        reg_list = []
        for register in range(temp_reg_size[-1]):
            register = f"t{register}"
            if register not in temp_registers[-1]:
                res += f"save {register}\n"
                reg_list.append(register)

        res += f"call C_{self.constructor_invoked}\n"

        for register in reg_list:
            res += f"restore {register}\n"

        for index in range(len(self.child1),-1,-1):
            res += f"restore a{index}\n"
        # res += f"restore a0\n"

        res+= "# End of new object expr:\n"
        return res

    def T(self):
        return self.temp

    def get_offset(self):
        res = ""
        temp = new_temp_reg()
        if self.offset != -5:
            res += f"move_immed_i {temp}, {self.offset}\n"
        else:
            res += f"move {temp}, a0\n"
        return res, temp



# x
class ThisExpr(Node):
    def __init__(self, current_class, line):
        super().__init__()
        self.line = line
        self.type = TypeNode(current_class, 'user')

    def __str__(self):
        return f"This"

    def code(self):
        self.temp = new_temp_reg()
        self.offset = -5
        res = "# Start this expr\n"
        res += f"move {self.temp}, a0\n"
        res += "# End this expr\n"
        return res

    def T(self):
        return self.temp

    def get_offset(self):
        res = ""
        return res, self.temp



# x
class SuperExpr(Node):
    def __init__(self, current_class, line):
        super().__init__()
        self.line = line
        B = my_classes[current_class]['parent']

        if B is None:
            self.type = TypeNode(' error', 'user')
            error(line, f"No Super class")
        else:
            self.type = TypeNode(B, 'user')

    def __str__(self):
        return f"Super"

    def code(self):
        self.temp = new_temp_reg()
        self.offset = -5
        res = "# Start super expr\n"
        res += f"move {self.temp}, a0\n"
        res += "# End super expr\n"
        return res

    def T(self):
        return self.temp

    def get_offset(self):
        res = ""
        return res, self.temp

# x
class ClassReferenceExpression(Node):
    def __init__(self, name, line):
        super().__init__()
        self.line = line
        self.class_name = name

        if name in my_classes:
            self.type = TypeNode(name, 'class_literal')
            self.class_ref = my_classes[name]['class ref']
        else:
            self.type = TypeNode(' error', 'constant')
            error(line, f"ClassReferenceExpression: Name not found: {name}")

    def __str__(self):
        return f"Class-reference({self.class_name})"

    def code(self):
        return ""

    def T(self):
        return ""

