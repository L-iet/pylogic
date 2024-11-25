from typing import TypedDict

Settings = TypedDict(
    "Settings",
    {
        "SHOW_VARIABLE_DEPS": bool,
        "SHOW_ALL_PARENTHESES": bool,
        "PYTHON_OPS_RETURN_PROPS": bool,
        "USE_CLASSICAL_LOGIC": bool,
    },
)

settings: Settings = {
    "SHOW_VARIABLE_DEPS": False,  # whether to show the dependencies of a variable in the string representation of a formula (True) or not (False)
    "SHOW_ALL_PARENTHESES": False,  # whether to show all parentheses in the string representation of a formula (True) or only the necessary ones (False)
    # whether python operators <, <=, >, >=, >>, &, |, ^, in, ~, should return propositions (True) or boolean values if implemented (False)
    "PYTHON_OPS_RETURN_PROPS": False,  # == always returns a bool because it is called by set.__contains__
    "USE_CLASSICAL_LOGIC": True,  # whether to use classical logic (True) or intuitionistic logic (False)
}
