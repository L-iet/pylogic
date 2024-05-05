from sympy import StrPrinter, Basic
from sympy.printing.latex import LatexPrinter

str_printer = StrPrinter({"order": "none"})
latex_printer = LatexPrinter({"order": "none"})


def str_print_order(expr) -> str:
    """
    Return the string representation of the expression with the order of the
    terms preserved.
    """
    if isinstance(expr, Basic):
        return str_printer.doprint(expr)
    return str(expr)


def latex_print_order(expr) -> str:
    """
    Return the latex representation of the expression with the order of the
    terms preserved.
    """
    if isinstance(expr, Basic):
        return latex_printer.doprint(expr)
    return expr._latex()
