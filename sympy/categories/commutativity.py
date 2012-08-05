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
from sympy import zeros, Matrix, Dict
from itertools import product

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

    [???] TODO: Add a reference to the formal proof.
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
        Fills in the adjacency matrix ``adj_matrix``.  Returns the
        corresponding *_edge_morphisms mapping, the input degrees of
        the vertices, and the output degree of the vertices as lists
        of numbers.

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

        in_degrees = [0] * len(diagram.objects)
        out_degrees = list(in_degrees)

        # We only work with finite diagrams here, this is why we can
        # simply iterate over all morphisms.
        for m in morphisms:
            dom_idx = obj_idx[m.domain]
            cod_idx = obj_idx[m.codomain]

            # Note that we are not computing the degree of the
            # vertices in the graph which we will eventually build
            # from the diagram.  Instead, we compute the degrees as
            # they are in the original multigraph.  That's because
            # these degrees will only be used to initialise the matrix
            # M_0, and at that point we would like to be as close as
            # possible to the multigraph situation.
            out_degrees[dom_idx] += 1
            in_degrees[cod_idx] += 1

            adj_matrix[dom_idx, cod_idx] = 1

            edge = (dom_idx, cod_idx)
            if edge in edge_morphisms:
                edge_morphisms[edge].append(m)
            else:
                edge_morphisms[edge] = [m]

        return edge_morphisms, in_degrees, out_degrees

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
    pattern_info = build_adj_matrix_edge_morphisms(
        pattern, pattern_obj_idx, pattern_adj_matrix, only_generators=True)
    pattern_edge_morphisms, pattern_in_degrees, pattern_out_degrees = pattern_info

    model_info = build_adj_matrix_edge_morphisms(
        model, model_obj_idx, model_adj_matrix, only_generators=False)
    model_edge_morphisms, model_in_degrees, model_out_degrees = model_info

    # `M_0` is set up similarly to the instructions for digraphs in
    # [Ullm1976], p 9.  The difference arises because [Ullm1976] talks
    # about digraphs, while finite diagrams are directed multigraphs.
    # See ``subgraph_isomorphisms`` for further details.
    npattern = len(pattern.objects)
    nmodel = len(model.objects)
    M_0 = zeros(npattern, nmodel)
    for v_p in xrange(npattern):
        for v_m in xrange(nmodel):
            if (pattern_in_degrees[v_p] <= model_in_degrees[v_m]) and \
               (pattern_out_degrees[v_p] <= model_out_degrees[v_m]):
                # v_p in the pattern and v_m in the model could be
                # mapped to each other in an isomorphism.
                #
                # Intuitively, since the vertex ``v_m`` in the model
                # graph has more ingoing and outgoing edges, we could
                # "put" the vertex ``v_p`` and all its adjacent edges
                # "over" the vertex ``v_m`` such that all of ``v_p``'s
                # edges math some of ``v_m``'s edges.
                M_0[v_p, v_m] = 1

    def is_subgraph_isomorphism(M, A, B):
        """
        Given the adjacency matrix of the pattern (``A``), of the
        model (``B``) and a matrix ``M``, checks whether ``M`` defines
        an embedding of the graph defined by ``A`` into the graph
        defined by ``B``.

        In other words, this function checks condition (1) from
        [Ullm1976].  Note that, as different from this source, in
        computing `C`, _one more_ transposition is made.  In other
        words, this function actually computes the _transposed_
        version of the `C` shown in [Ullm1976].  The reason is
        formally explained in [???].
        """
        C = (M * (M * B).transpose()).transpose()

        for i in xrange(A.rows):
            for j in xrange(A.cols):
                if (A[i, j] == 1) and (C[i, j] == 0):
                    return False
        return True

    # Note that while this code follows [Ullm1976] as closely as
    # possible, the correspondence between the steps in the article
    # and the steps in this function should not be considered
    # strict.

    # Step 1.

    # This vector will describe which vertices have already been
    # mapped to.  ``F[i] == True`` means that some vertex of the
    # pattern has already been mapped to the vertex ``i`` of the
    # model.
    F = [False] * nmodel

    def subgraph_isomorphisms(M, d, F):
        """
        Applies Ullman's algorithm for subgraph isomorphisms.  This
        function returns a generator which will enumerate all matrices
        `M'` representing all possible subgraph isomorphisms
        (embeddings).

        This is the implementation of the very first algorithm shown
        in [Ullm1976], slightly modified to fit naturally with the
        recursion.  The sequence of steps Ullman describes is actually
        a simulation of recursion and a couple loops, using a very
        basic goto-based language abstraction.

        A fundamental notion in Ullman's algorithm is the matrix `M`,
        which represents a mapping from the set of vertices of the
        pattern into the set of vertices of the model.  `M_{ij} = 1`
        if vertex `i` of the pattern is mapped to vertex `j` of the
        model.

        ``M`` represents the matrix `M`, which is processed line by
        line, to eventually construct the matrix `M'`.  One recursive
        call tries all possible configurations for a line of `M`, and,
        for each such configuration, spawns a new recursive call,
        which processes the next line.  When the bottom of the matrix
        is reached, this function checks whether `M'` is indeed an
        embedding.

        ``d`` corresponds to `d` in [Ullm1976] and represents the
        index of the line which is being processed in this call.  The
        array ``F`` corresponds to `F`.  ``M_d`` is not an array, as
        in [Ullm1976], but is instead a simple local variable.  We
        assure the coexistence of the necessary amount of `M_d` values
        by reallocating ``M_d``'s at each recursive call.

        `H_d` from [Ullm1976] is not represented by anything.  Note
        that, in the article, there is only one instance of `k`.  When
        the algorithm moves from line `d` to line `d+1` (a recursive
        call, in this implementation), it needs to store the value of
        `k` at which is stopped when it was processing line `d`;
        that's what `H_d` is used for.  In this implementation, it is
        not necessary, because ``k`` is an individual variable, local
        to each new recursive call.
        """
        # Step 2.

        # This is actually just a copy of ``M``.
        M_d = Matrix(M)

        # Step 3.
        for k in xrange(0, nmodel):
            if (M[d, k] == 0) or F[k]:
                # Either mapping the vertex ``d`` of the pattern to
                # the vertex ``k`` of the model is impossible, or
                # vertex ``k`` has already been mapped to.
                continue

            # In the current line (``d``), set all elements save
            # ``M[d, k]`` to 0.
            for j in xrange(0, k):
                M[d, j] = 0
            for j in xrange(k + 1, nmodel):
                M[d, j] = 0

            # Step 4, the else part of the sentence.
            if d == npattern - 1:
                # We have just completed another matrix, which might be an
                # isomorphism.  Let's check that (cf. condition (1) in
                # [Ullm1976]).
                if is_subgraph_isomorphism(
                    M, pattern_adj_matrix, model_adj_matrix):
                    yield M
            else:
                # Step 6.
                F[k] = True

                # We need to explicitly re-yield the results from that
                # recursive generator.
                for M in subgraph_isomorphisms(M, d + 1, F):
                    yield M

                F[k] = False

            # Step 5.

            # Try to set another column in this row to zero.
            M = Matrix(M_d)

        # Step 7.
        return

    def match_morphisms(pattern_morphisms, model_morphisms, morphism_mapping):
        """
        Produces all property-based matches between two lists of
        morphisms.

        It is supposed that the edge of the pattern, to which
        ``pattern_morphisms`` is associated, is mapped by graph
        embedding, to the edge of the model, to which
        ``model_morphisms`` is associated.  This function does not
        check this condition, however.

        ``morphism_mapping`` is the accumulator which will contain one
        of the sought mappings in every terminal case of recursion.
        """
        if not pattern_morphisms:
            # We have finished constructing the match.
            yield dict(morphism_mapping)
            return

        pattern_morphism = pattern_morphisms[0]
        pattern_tail = pattern_morphisms[1:]

        for model_morphism in model_morphisms:
            if model[model_morphism] == pattern[pattern_morphism]:
                # Yay, another match.
                morphism_mapping[pattern_morphism] = model_morphism

                # Copy ``model_morphisms`` and drop the found match.
                model_morphisms_ = list(model_morphisms)
                model_morphisms_.remove(model_morphism)

                for mapping in match_morphisms(pattern_tail, model_morphisms_,
                                               morphism_mapping):
                    yield mapping

    for M in subgraph_isomorphisms(M_0, 0, F):
        # Decode ``M`` into actual vertex mapping.
        mapping = [None] * npattern
        for v_p in xrange(M.rows):
            # Note that there is exactly one 1 in every row of M.
            for j in xrange(M.cols):
                if M[v_p, j] == 1:
                    mapping[v_p] = j
                    break

        # Collect the generators for morphism mappings for each edge.
        morphism_mappings = []
        for (v_pattern, w_pattern), pattern_morphisms in \
                pattern_edge_morphisms.items():
            # See to what edge this is mapped in the model, and get
            # the corresponding morphisms in the model.
            v_model = mapping[v_pattern]
            w_model = mapping[w_pattern]
            model_morphisms = model_edge_morphisms[(v_model, w_model)]

            morphism_mapping = match_morphisms(pattern_morphisms,
                                               model_morphisms, {})

            morphism_mappings.append(morphism_mapping)

        # Finally, generate all morphism embeddings.  Note that now we
        # only know how the _generator morphisms_ of the pattern are
        # mapped into the model, so we are not producing full diagram
        # embeddings as of yet.
        #
        # Remember that ``morphism_mappings`` is a list of generators,
        # with a generator per edge of the pattern.  Each generator
        # produces all possible property-preserving mappings between
        # the set of morphisms, associated with an edge in the
        # pattern, and the set of morphisms of the corresponding edge
        # in the model.  We would like to produce the Cartesian
        # product of all these generators, which will represent an
        # embedding of the pattern into the model.
        for embedding_tuple in product(*morphism_mappings):
            # ``embedding_tuple`` is an element of the Cartesian
            # product of the generators, i.e., it's a tuple of dicts.
            # Squash the all those dicts into one big dictionary.
            generator_embedding = {}
            for morphism_mapping in embedding_tuple:
                generator_embedding.update(morphism_mapping)
