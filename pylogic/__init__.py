import sys

if not sys.warnoptions:
    import warnings

    from pylogic.warn import PylogicInternalWarning

    warnings.simplefilter("ignore", PylogicInternalWarning)
