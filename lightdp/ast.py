from __future__ import print_function


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
        return self.__class__.__name__ + ': ' + self.value

    def children(self):
        return ()


class FunctionCall:
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self):
        return self.__class__.__name__ + ': ' + self.name

    def children(self):
        return self.args


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
