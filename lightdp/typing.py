import pysmt.typing


class NumType:
    def __init__(self, value):
        self.value = value

    def __eq__(self, other):
        return self.value == other.value


class ListType:
    def __init__(self, elem_type):
        self.elem_type = elem_type

    def __eq__(self, other):
        return isinstance(other, ListType) and self.elem_type == other.elem_type


class BoolType:
    def __init__(self):
        pass

    def __eq__(self, other):
        return isinstance(other, BoolType)


class FunctionType:
    def __init__(self, para_type, return_type):
        self.para_type = para_type
        self.return_type = return_type

    def __eq__(self, other):
        return isinstance(other, FunctionType) and \
               self.para_type == other.para_type and \
               self.return_type == other.return_type


def to_smt_type(lightdp_type):
    if isinstance(lightdp_type, NumType):
        return pysmt.typing.REAL
    elif isinstance(lightdp_type, ListType):
        return pysmt.typing.ArrayType(pysmt.typing.REAL, to_smt_type(lightdp_type.elem_type))
    elif isinstance(lightdp_type, FunctionType):
        return pysmt.typing.FunctionType(to_smt_type(lightdp_type.return_type), to_smt_type(lightdp_type.para_type))
    elif isinstance(lightdp_type, BoolType):
        return pysmt.typing.BOOL
