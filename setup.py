from setuptools import find_packages, setup

setup(
    name="pylogic",
    packages=find_packages(),
    version="0.1.0",
    description="Pylogic: A mathematical proof assistant in Python",
    author="Joshua Mark",
    install_requires=["sympy", "mpmath"]
)