import ast


_noise_functions = ('Laplace', )


class NodeTransformer(ast.NodeTransformer):
    def visit_Module(self, node):
        new_node = self.generic_visit(node)
        new_node.body.insert(0, ast.FunctionDef(name='havoc',
                                                args=ast.arguments(
                                                    args=[ast.Name(id='scale', ctx=ast.Param())],
                                                    vararg=None,
                                                    kwarg=None,
                                                    defaults=[]),
                                                decorator_list=[],
                                                body=[ast.Expr(value=ast.Str('Implement the havoc instruction here')),
                                                      ast.Pass()]
                                                ))
        return new_node

    def visit_FunctionDef(self, node):
        new_node = self.generic_visit(node)
        # TODO: determine whether it's the function to transform or not
        # remove the annotation string
        new_node.body = new_node.body[1:]
        new_node.body.insert(0, ast.Assign(targets=[ast.Name(id='__V_epsilon', ctx=ast.Store())], value=ast.Num(0)))

        return new_node

    def visit_Assign(self, node):
        if isinstance(node.value, ast.Call) \
                and isinstance(node.value.func, ast.Name) \
                and node.value.func.id in _noise_functions:
            node.value.func.id = 'havoc'
            change_v_epsilon = ast.AugAssign(target=ast.Name(id='__V_epsilon', ctx=ast.Store()), op=ast.Add(),
                                             value=ast.BinOp(left=ast.Num(1.0), op=ast.Div(), right=node.value.args[0]))
            return change_v_epsilon, node
        else:
            return node

    def visit_Return(self, node):
            node.value = ast.Tuple(elts=[node.value, ast.Name(id='__V_epsilon', ctx=ast.Load())], ctx=ast.Load())
            return node

    def generic_visit(self, node):
        new_node = super(NodeTransformer, self).generic_visit(node)
        if hasattr(new_node, 'body') and isinstance(new_node.body, (tuple, list)):
            # unpack the tuple that visit_Assign created
            unpacked_body = []
            for node in new_node.body:
                if isinstance(node, (tuple, list)):
                    for n in node:
                        unpacked_body.append(n)
                else:
                    unpacked_body.append(node)

            new_node.body = unpacked_body

        return new_node


def transform(node):
    transformer = NodeTransformer()
    if isinstance(node, list):
        final_ast = [transformer.visit(node[0])]
        for n in node[1:]:
            tree = transformer.visit(n)
            if isinstance(tree, ast.Module):
                # trim the 'def havoc(scale): pass' code for the rest
                tree.body = tree.body[1:]
            final_ast.append(tree)
        return final_ast
    else:
        return transformer.visit(node)

