class NumType:
    def __init__(self, value):
        self.value = value


class ListType:
    def __init__(self, elem_type):
        self.elem_type = elem_type


class BoolType:
    def __init__(self):
        pass


class FunctionType:
    def __init__(self, para_type, return_type):
        self.para_type = para_type
        self.return_type = return_type
