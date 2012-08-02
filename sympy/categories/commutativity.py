"""
This module contains the functionality pertaining to deciding the
commutativity of diagrams and diagrammatic implications (in the sense
of the classes :class:`Diagram` and :class:`Implication`).

TODO: Give more details about this and also some examples.

See Also
========
Diagram, Implication

References
==========

[Ullm1976] J. R. Ullman, An Algorithm for Subgraph Isomorphism,
J. Association of Computing Machinery, March, 1976, 16, 31--42.
"""

from sympy.categories import Diagram

def diagram_embeddings(pattern, model):
    """
    Generates all embeddings of the :class:`Diagram` ``pattern`` into
    the :class:`Diagram` ``model``.  An embedding must preserve
    morphism properties.  An embedding is represented as a dictionary
    which contains pairs of the form `(f_p, f_m)` where `f_p` runs
    through all morphisms of the ``pattern`` and `f_m` is the morphism
    of the model to which `f_p` is mapped.

    In case a diagram is infinite, only its expanded generators are
    considered.  For reasons explained in the docstring of
    :class:`Diagram`, this suffices to spot essentially all embeddings
    (all families of embeddings, formally speaking).

    References
    ==========

    [Ullm1976] J. R. Ullman, An Algorithm for Subgraph Isomorphism,
    J. Association of Computing Machinery, March, 1976, 16, 31--42.
    """
    pass
