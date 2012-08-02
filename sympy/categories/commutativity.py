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
from sympy import zeros

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
    def build_obj_idx(diagram):
        """
        Returns a tuple, which a mapping between objects and numeric
        indices and a mapping between numeric indices and objects
        (i.e., a list of objects).
        """
        # Since we only care that object indices are stable during the
        # runtime of this function, we don't really need any special
        # ordering on the objects of the diagram.
        obj_idx = list(diagram.objects)

        idx_obj = {}
        for i in xrange(len(obj_idx)):
            idx_obj[obj_idx[i]] = i

        return obj_idx, idx_obj

    pattern_idx_obj, pattern_obj_idx = build_obj_idx(pattern)
    model_idx_obj, model_obj_idx = build_obj_idx(model)

    pattern_adj_matrix = zeros(len(pattern.objects))
    model_adj_matrix = zeros(len(model.objects))

    def build_adj_matrix_edge_morphisms(diagram, obj_idx, adj_matrix,
                                        only_generators):
        """
        Fills in the adjacency matrix ``adj_matrix`` and returns the
        corresponding *_edge_morphisms mapping.

        If ``only_generators == True``, it builds the adjacency matrix
        based on the generators of the diagram.  Otherwise it uses the
        ``expanded_generators`` thereof (remember, expanded generators
        are our main weapon against infinite diagrams).

        An *_edge_morphisms dictionary maps a (directed) edge to the
        morphisms going between the same two objects in the same
        direction.  The edge is represented as a pair of object
        indices.
        """
        edge_morphisms = {}

        if only_generators:
            morphisms = diagram.generators
        else:
            morphisms = diagram.expanded_generators

        # We only work with finite diagrams here, this is why we can
        # simply iterate over all morphisms.
        for m in morphisms:
            dom_idx = obj_idx[m.domain]
            cod_idx = obj_idx[m.codomain]

            adj_matrix[dom_idx, cod_idx] = 1

            edge = (dom_idx, cod_idx)
            if edge in edge_morphisms:
                edge_morphisms[edge].append(m)
            else:
                edge_morphisms[edge] = [m]

        return edge_morphisms

    # We only consider the generators of ``model`` because all other
    # morphisms should be mapped in full accordance with how the
    # generators are mapped.  Thus, we will construct all embeddings
    # of the multigraph defined by the _generators of the pattern_
    # into the multigraph defined by the _expanded generators of the
    # model_.  This will guarantee that all other morphisms of the
    # pattern will have the necessary counterparts in the model
    # (because any diagram contains all compositions of all morphisms
    # it contains).  We will have to check the properties explicitly
    # though, because they can be explicitly specified for composites
    # and can thus be different from the intersection of properties of
    # the components.
    pattern_edge_morphisms = build_adj_matrix_edge_morphisms(
        pattern, pattern_obj_idx, pattern_adj_matrix, only_generators=True)
    model_edge_morphisms = build_adj_matrix_edge_morphisms(
        model, model_obj_idx, model_adj_matrix, only_generators=False)
