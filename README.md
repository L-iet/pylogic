# Pylogic

This is a simple proof assistant for propositional and higher-order logic. The goal is to be able to formalise some statements in undergrad math courses and prove them using this tool.

## Installation

Install Pylogic directly from Github using pip.

```bash
pip install "git+https://github.com/L-iet/pylogic.git"
```

To locally install, clone the repository and run:

```bash
pip install .
```

Otherwise, clone the repository, create a virtual environment, and install the dependencies:

Bash:
```bash
git clone https://github.com/L-iet/pylogic.git
cd pylogic
python -m venv venv
source venv/bin/activate
pip install -r requirements.txt
```

Windows Command Prompt:

```bash
git clone https://github.com/L-iet/pylogic.git
cd pylogic
python -m venv venv
venv\Scripts\activate
pip install -r requirements.txt
```

Importing Pylogic

After installing, check if Pylogic is w

orking by importing it. Open a Python interpreter or a Jupyter notebook and run:

```python
from pylogic import *
```

## Documentation

Read the current documentation [here](docs/Introduction.ipynb).

## Examples

Read a tutorial on how to use Pylogic [here](Tutorial%20Demo.ipynb)

View a basic example of a proof [here](Basic%20Examples.ipynb)

Look at some proofs written in Pylogic:

- [Proof of infinitely many primes](infinite_primes.ipynb)
- [Proof that an irrational to the power of an irrational can be rational](irr_to_power_irr.ipynb)
- [Proof of the nested interval property of the real numbers](nested_interval.ipynb)
- [Proof that the square root of 2 is irrational](root_2_is_irrational_1.ipynb)


## Dev Installation

- Ensure `wheel` is installed
- Clone the repo and run the following commands. Check the version of the wheel file in the `dist` folder and install it using pip.

```bash
python setup.py bdist_wheel
pip install dist/pylogic-{version}-py3-none-any.whl
```

