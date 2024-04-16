from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.and_ import And
from pylogic.proposition.or_ import Or
from pylogic.proposition.implies import Implies

tactics = {"Proposition": []}


def proof_search(premises: list[Proposition]):
    for prem in premises:
        cls = str(prem.__class__).split(".")[-1]
