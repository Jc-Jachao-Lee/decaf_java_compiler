# decaf_absmc

# AST codegen is made of two parts.
# node.t() and node.code()
# node.t() stores the return value of an expression (What this means is the register you would want to access)
# for ex for an assignment statement, we would get register that the value would be assigned into following the code
# node.code() stores the code of both expressions and statements

arg_reg_size = [0]
temp_reg_size = [0]
arg_registers = [[]]
# made up of
temp_registers = [[]]

# base address, size
# use tuples as the key: (object name, field)
heap_size = -1
static_data_size = 0

# i do not think these two will have any functionality
control_stack = []
data_stack = []

# types : vars_i : offsets
offsets={}
variable_offset_finder = {}

# type 0 means that it is immediately safe to user
# type 1 means that this register is writing over something else
def new_temp_reg():
    '''temp_registers[-1][var] = f't{temp_reg_index[-1]}'
    temp_reg_index[-1] += 1
    return temp_registers[var]'''
    if len(temp_registers[-1]):
        register = temp_registers[-1].pop()
        return register
    else:
        temp_reg_size[-1] += 1
        return f't{temp_reg_size[-1]-1}'


def destroy_temp(reg):
    if reg not in temp_registers[-1]:
        temp_registers[-1].append(reg)


def enter_function():
    temp_registers.append([])
    temp_reg_size.append(0)
    arg_registers.append([])
    arg_reg_size.append(0)


def leave_function():
    temp_registers.pop()
    temp_reg_size.pop()
    arg_registers.pop()
    arg_reg_size.pop()


def new_static():
    global static_data_size
    static_data_size += 1
    return static_data_size-1


def new_dynamic():
    global heap_size
    #print(f"heap_top: {heap_size}")
    heap_size += 1
    return heap_size-1


def assemble(program, file_name):
    str = program.code()
    # print(str)
    with open(f"{file_name}.ami", 'w') as file:
        file.write(str)
