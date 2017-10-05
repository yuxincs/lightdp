from __future__ import print_function
from six import string_types


class Block:
    def __init__(self, statements):
        self.statements = statements

    def __str__(self):
        return self.__class__.__name__

    def children(self):
        return self.statements


class Function:
    def __init__(self, declaration, body):
        self.declaration = declaration
        self.body = body

    def __str__(self):
        return self.__class__.__name__

    def children(self):
        return self.declaration, self.body


class FunctionDeclaration:
    def __init__(self, name, args, returns):
        self.name = name
        self.args = args
        self.returns = returns

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.name

    def children(self):
        return self.args + [self.returns]


class While:
    def __init__(self, condition, body):
        self.condition = condition
        self.body = body

    def __str__(self):
        return self.__class__.__name__

    def children(self):
        return self.condition, self.body


class If:
    def __init__(self, condition, body, else_body):
        self.condition = condition
        self.body = body
        self.else_body = else_body

    def __str__(self):
        return self.__class__.__name__

    def children(self):
        return (self.condition, self.body, self.else_body) if self.else_body is not None else (self.condition, self.body)


class TypeDeclaration:
    def __init__(self, names, type):
        self.names = names
        self.type = type

    def __str__(self):
        return self.__class__.__name__

    def children(self):
        return self.names + [self.type]


class Type:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return self.__class__.__name__ + ': ' \
               + (self.left if isinstance(self.left, string_types) else '') \
               + (' ' + self.right if isinstance(self.right, string_types) else '')

    def children(self):
        return list(filter(lambda x: x is not None and not isinstance(x, string_types), [self.left, self.right]))


class BinaryOperation:
    def __init__(self, operator, left, right):
        self.operator = operator
        self.left = left
        self.right = right

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.operator

    def children(self):
        return self.left, self.right


class UnaryOperation:
    def __init__(self, operator, operand):
        self.operator = operator
        self.operand = operand

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.operator

    def children(self):
        return self.operand,


class Variable:
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.name

    def children(self):
        return ()


class Real:
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return self.__class__.__name__ + ': ' + str(self.value)

    def children(self):
        return ()


class Boolean:
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return self.__class__.__name__ + ': ' + str(self.value)

    def children(self):
        return ()


class FunctionCall:
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.name

    def children(self):
        return (self.args,) if self.args is not None else ()


class ListIndex:
    def __init__(self, name, index):
        self.name = name
        self.index = index

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.name

    def children(self):
        return self.index,


class ConditionalVariable:
    def __init__(self, condition, true, false):
        self.condition = condition
        self.true = true
        self.false = false

    def __str__(self):
        return self.__class__.__name__

    def children(self):
        return self.condition, self.true, self.false


class Assign:
    def __init__(self, name, expression):
        self.name = name
        self.expression = expression

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.name

    def children(self):
        return self.expression,


def render(node):
    def _render(node, level):
        for i in range(level):
            if i == 0 or i % 4 == 0:
                print('|', end='')
            else:
                print('-', end='')
        print(node)
        for child in node.children():
            _render(child, level + 4)

    _render(node, 0)
