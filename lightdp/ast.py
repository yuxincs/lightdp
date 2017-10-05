function_map = {
    'Lap': 'lightdp.distribution.lap'
}


def _indent(depth=0):
    return '  ' * depth


class Function:
    def __init__(self, name, args, returns, body):
        assert isinstance(body, list)
        self.name = name
        self.args = args
        self.returns = returns
        self.body = body

    def transform(self, depth=0):
        args_str = [arg.transform() for arg in self.args]
        s = _indent(depth) + 'def ' + self.name + '(' + ','.join(args_str) + '):\n'
        # add return variable declarations
        for arg in self.returns:
            init_value = '[]' if arg.type.left == 'list' else '0.0'
            s += _indent(depth + 1) + '\n'.join([name.transform() + ' = ' + init_value for name in arg.names]) + '\n'

        s += '\n'.join([stmt.transform(depth + 1) for stmt in self.body]) + '\n'

        # add return statement
        s += _indent(depth + 1) + 'return ' + ','.join([arg.transform() for arg in self.returns])
        return s


class While:
    def __init__(self, condition, body):
        assert isinstance(body, list)
        self.condition = condition
        self.body = body

    def transform(self, depth=0):
        s = _indent(depth) + 'while ' + self.condition.transform() + ':\n'
        s += '\n'.join([stmt.transform(depth + 1) for stmt in self.body])
        return s


class If:
    def __init__(self, condition, body, else_body):
        assert isinstance(body, list)
        assert isinstance(else_body, list)
        self.condition = condition
        self.body = body
        self.else_body = else_body

    def transform(self, depth=0):
        s = _indent(depth) + 'if ' + self.condition.transform() + ':\n'
        s += '\n'.join([stmt.transform(depth + 1) for stmt in self.body]) + '\n'
        s += _indent(depth) + 'else:\n'
        s += '\n'.join([stmt.transform(depth + 1) for stmt in self.else_body])
        return s


class TypeDeclaration:
    def __init__(self, names, type):
        assert isinstance(names, list)
        self.names = names
        self.type = type

    def transform(self, depth=0):
        return _indent(depth) + ','.join([name.transform() for name in self.names])


class Type:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def transform(self, depth=0):
        # currently we won't transform type instructions
        assert False


class BinaryOperation:
    def __init__(self, operator, left, right):
        self.operator = operator
        self.left = left
        self.right = right

    def transform(self, depth=0):
        left = self.left.transform() \
            if isinstance(self.left, Variable) or isinstance(self.left, Real) or isinstance(self.left, Boolean) \
            else '(' + self.left.transform() + ')'
        right = self.right.transform() \
            if isinstance(self.right, Variable) or isinstance(self.right, Real) or isinstance(self.right, Boolean) \
            else '(' + self.right.transform() + ')'
        if self.operator == '::':
            return _indent(depth) + right + '.append(' + left + ')'
        else:
            return _indent(depth) + left + ' ' + self.operator + ' ' + right


class UnaryOperation:
    def __init__(self, operator, operand):
        self.operator = operator
        self.operand = operand

    def transform(self, depth=0):
        return _indent(depth) + self.operator + self.operand.transform()


class Variable:
    def __init__(self, name):
        self.name = name

    def transform(self, depth=0):
        return _indent(depth) + self.name


class Real:
    def __init__(self, value):
        self.value = value

    def transform(self, depth=0):
        return _indent(depth) + str(self.value)


class Boolean:
    def __init__(self, value):
        self.value = value

    def transform(self, depth=0):
        return _indent(depth) + str(self.value)


class FunctionCall:
    def __init__(self, name, args):
        assert isinstance(args, list)
        self.name = name
        self.args = args

    def transform(self, depth=0):
        return _indent(depth) + function_map.get(self.name, self.name) + '(' + ','.join([arg.transform() for arg in self.args]) + ')'


class ListIndex:
    def __init__(self, name, index):
        self.name = name
        self.index = index

    def transform(self, depth=0):
        return _indent(depth) + self.name + '[' + self.index.transform() + ']'


class ConditionalVariable:
    def __init__(self, condition, true, false):
        self.condition = condition
        self.true = true
        self.false = false

    def transform(self, depth=0):
        return _indent(depth) + self.true.transform() + ' if ' + self.condition.transform() + ' else '+ self.false.transform()


class Assign:
    def __init__(self, name, expression):
        self.name = name
        self.expression = expression

    def transform(self, depth=0):
        return _indent(depth) + self.name + ' = ' + self.expression.transform()


def transform(statements):
    s = 'import lightdp\n\n'
    s += '\n'.join([stmt.transform() for stmt in statements])
    return s
