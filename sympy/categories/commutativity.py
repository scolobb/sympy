"""
This module contains the functionality pertaining to deciding the
commutativity of diagrams and diagrammatic implications (in the sense
of the classes :class:`Diagram` and :class:`Implication`).
n
TODO: Give more details about this and also some examples.

See Also
========
Diagram, Implication

References
==========

[Ullm1976] J. R. Ullman, An Algorithm for Subgraph Isomorphism,
J. Association of Computing Machinery, March, 1976, 16, 31--42.
"""

from sympy.categories import Diagram, CompositeMorphism
from sympy import zeros, Matrix, Dict
from itertools import product, combinations

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
            # Not only do we want the generators of the diagram, but
            # also only those generators, which are not composites.
            # ``Diagram`` does not simplify all such morphisms out,
            # such morphisms may have some additional properties.  We
            # do not really care about that here, however.  Properties
            # will be addressed at a later time.
            morphisms = [m for m in diagram.generators
                         if not isinstance(m, CompositeMorphism)]
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

    def check_refinement_condition(M, A, B, i, j):
        """
        Given the adjacency matrix of the pattern (``A``), of the
        model (``B``) and a matrix ``M``, checks the modified
        condition (2) from [Ullm1976] for the element `M_{ij}`.  The
        modified condition (2) is on page 9.

        This function and the next two functions all apply the
        refinement procedure.  The idea behind splitting the code up
        this much is to keep everything as intelligible as possible.

        If the refinement condition holds, then `M_{ij}` is _not_
        changed to 0.
        """
        # Condition 2 consists of two cases, both of which are
        # formulated like "for every `x` there is `y`", this is why we
        # will check both cases separately, but in the same two nested
        # loops.
        for x in xrange(npattern):
            # There's a fine subtlety in checking the conditions.  If
            # there is no `x` such that `A_{ix} = 1`, the first case
            # of the condition is actually true.  Ditto for `A_{xi}`.

            if A[i, x] == 0:
                # No such edge `(i, x)` in the pattern.  Fine, this
                # case is true.
                case_1 = True
            else:
                # Additional check required.
                case_1 = False

            if A[x, i] == 0:
                # No such edge `(x, i)` in the pattern.  Fine, this
                # case is true.
                case_2 = True
            else:
                # Additional check required.
                case_2 = False

            for y in xrange(nmodel):
                # Case 1.
                if not case_1 and (A[i, x] == 1) and (M[x, y] * B[j, y] == 1):
                    case_1 = True
                # Case 2.
                if not case_2 and (A[x, i] == 1) and (M[x, y] * B[y, j] == 1):
                    case_2 = True

            if not case_1 or not case_2:
                return False

        return True

    def refine_one_step(M, A, B):
        """
        Given the adjacency matrix of the pattern (``A``), of the
        model (``B``) and a matrix ``M``, applies one iteration of the
        refinement procedure from [Ullm1976].

        The idea behind the refining procedure is to look ahead a bit
        and cut off those mappings which will definitely not bring us
        to an isomorphism.

        This function will also check if there are rows that contain
        no ones.  If this is the case, it will return ``False``;
        otherwise, it will return ``True``.  (Judging by the current
        test coverage, it looks like this check may just be redundant;
        however, I'd prefer keeping it in order to stay on the safe
        side (since [Ullm1976] does do it as well))

        The side effects (i.e., modifying ``M`` and returning a flag
        at the same time) are the result of an attempt to follow
        [Ullm1976] as closely as possible.
        """
        for i in xrange(M.rows):
            empty_row = True
            for j in xrange(M.cols):
                if (M[i, j] == 1):
                    empty_row = False
                    if not check_refinement_condition(M, A, B, i, j):
                        M[i, j] = 0

            if empty_row:
                return False

        return True

    def refine(M, A, B):
        """
        Given the adjacency matrix of the pattern (``A``), of the
        model (``B``), and a matrix ``M``, applies the full refinement
        procedure from [Ullm1976].

        This function calls ``refine_one_step`` until there are
        changes to ``M``.
        """
        M_last = Matrix(M)

        # Mind the side effects!
        if not refine_one_step(M, A, B):
            return False

        while M != M_last:
            # Mind the side effects!
            if not refine_one_step(M, A, B):
                return False

            M_last = Matrix(M)

        return True

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

            # Mind the side effects!
            if not refine(M, pattern_adj_matrix, model_adj_matrix):
                # Try to set other columns in this row to zero.
                M = Matrix(M_d)
                continue

            # Step 4, the else part of the sentence.
            if d == npattern - 1:
                # We have just completed another matrix, which is an
                # isomorphism.  We do not need to check this, because
                # applying the refinement procedure guarantees that
                # [Ullm1976].
                #
                # Essentially, if `M` hadn't been an isomorphism, we
                # would have skipped it in the if statement invoking
                # ``refine``.
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
            if model[model_morphism].subset(pattern[pattern_morphism]):
                # Yay, another match.
                morphism_mapping[pattern_morphism] = model_morphism

                # Copy ``model_morphisms`` and drop the found match.
                model_morphisms_ = list(model_morphisms)
                model_morphisms_.remove(model_morphism)

                for mapping in match_morphisms(pattern_tail, model_morphisms_,
                                               morphism_mapping):
                    yield mapping

    def map_composite(pattern_composite, generator_embedding):
        """
        Given a composite morphism in the pattern and the embeddings
        of the generators, produces the corresponding composite
        morphism in the model.
        """
        return CompositeMorphism([generator_embedding[component]
                                  for component in pattern_composite])

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

            # The last step is to walk through all composites in the
            # pattern and check how whether there counterparts in the
            # model have the necessary properties.

            # We will keep the embeddings of the composites in a
            # separate dictionary, to make it easier for
            # ``map_composite`` to dig up its information.
            composite_embedding = {}
            good_embedding = True
            for pattern_morphism in pattern.expanded_generators:
                if isinstance(pattern_morphism, CompositeMorphism):
                    model_composite = map_composite(pattern_morphism,
                                                    generator_embedding)
                    if model[model_composite].subset(pattern[pattern_morphism]):
                        composite_embedding[pattern_morphism] = model_composite
                    else:
                        # This is bad news, but this embedding does
                        # not fit.
                        good_embedding = False
                        break

            if good_embedding:
                # Everything done here; just merge the two
                # dictionaries and yield them.
                embedding = dict(generator_embedding)
                embedding.update(composite_embedding)
                yield Dict(embedding)

def _unroll_composites(morphisms):
    """
    Given a collection of morphisms ``morphisms``, picks apart all
    composites and lists their components instead.
    """
    new_morphisms = []
    for m in morphisms:
        if isinstance(m, CompositeMorphism):
            new_morphisms.extend(m.components)
        else:
            new_morphisms.append(m)
    return new_morphisms

def _check_commutativity_with_diagrams(diagram, commutative_diagrams,
                                       commutative_regions = ()):
    """
    Given a :class`Diagram` and a collection of :class:`Diagram`'s
    known to be commutative, decides whether ``diagram`` is
    commutative.

    ``commutative_regions`` can be used to specify subdiagrams of
    ``diagram`` which are already known to be commutative.

    This is known as the commutativity stage of inference [???].

    TODO: Explain why we don't care about morphism properties in this
    function.

    References
    ==========

    [???] TODO: Add a reference to the blog post.
    """
    def reachable_objects(base_obj, diagram):
        """
        Returns the set of objects in ``diagram`` reachable from
        ``object``.
        """
        # We will trust ``Diagram.is_hom_set_empty`` to be
        # sufficiently efficient.
        reachable = set([])
        for obj in diagram.objects:
            if not diagram.is_hom_set_empty(base_obj, obj):
                reachable.add(obj)
        return reachable

    def reverse_reachable_objects(base_obj, diagram):
        """
        Returns the set of objects in ``diagram`` from which
        ``object`` is reachable .
        """
        # We will trust ``Diagram.is_hom_set_empty`` to be
        # sufficiently efficient.
        reverse_reachable = set([])
        for obj in diagram.objects:
            if not diagram.is_hom_set_empty(obj, base_obj):
                reverse_reachable.add(obj)
        return reverse_reachable

    def can_subdiagrams_be_merged(subdiagram1, subdiagram2,
                                  commutative_subdiagrams):
        """
        Checks if two commutative subdiagrams can be merged.

        Two commutative subdiagrams can be merged if they have a
        common commutative subdiagram and the following condition
        holds.  Consider a pair of objects `C_1` and `C_2` in the
        common subdiagram for which there exists `A` in one of the
        subdiagrams and `B` in the other one such that there exist two
        different composite morphisms `f_1, f_2:A\rightarrow B`, where
        `f_1` passes through `C_1` and `f_2` passes through `C_2`.  To
        be able to merge two such subdiagrams `C_1` and `C_2` should
        be connected with a morphism in the common subdiagram.

        See [???] for a more detailed explanation and formal proof.

        TODO: Add a reference to the blog post.
        """
        common_subdiagram = Diagram(set(subdiagram1.generators) &
                                    set(subdiagram2.generators))
        if not common_subdiagram.generators:
            return False

        if not any(common_subdiagram <= commutative_subdiagram
                   for commutative_subdiagram in commutative_subdiagrams):
            # ``common_subdiagram`` is not contained in any of the
            # subdiagrams known to be commutative.
            return False

        common_objects = common_subdiagram.objects

        # Collect the reachability information for the common objects.
        # Note that we have to collect that information in _both_
        # subdiagrams.
        reachability1 = {}
        reachability2 = {}
        reverse_reachability1 = {}
        reverse_reachability2 = {}
        for obj in common_objects:
            reachability1[obj] = reachable_objects(obj, subdiagram1)
            reachability2[obj] = reachable_objects(obj, subdiagram2)
            reverse_reachability1[obj] = reverse_reachable_objects(
                obj, subdiagram1)
            reverse_reachability2[obj] = reverse_reachable_objects(
                obj, subdiagram2)

        # Go through all pairs of common objects and check whether
        # those pairs for which `f_1` and `f_2` exist (see the
        # docstring) are connected with something in at least one of
        # the subdiagrams.
        for (obj1, obj2) in combinations(common_objects, 2):
            # This shows whether there are morphisms starting in
            # ``subdiagram2`` and ending in ``subdiagram1``.
            direction1 = (reachability1[obj1] & reachability1[obj2]) and \
                         (reverse_reachability2[obj1] &
                          reverse_reachability2[obj2])

            # This shows the reverse: whether there are morphisms
            # starting in ``subdiagram1`` and ending in
            # ``subdiagram2``.
            direction2 = (reachability2[obj1] & reachability2[obj2]) and \
                         (reverse_reachability1[obj1] &
                          reverse_reachability1[obj2])

            if direction1 or direction2:
                if common_subdiagram.is_hom_set_empty(obj1, obj2) and \
                   common_subdiagram.is_hom_set_empty(obj2, obj1):
                    # ``obj1`` and ``obj2`` should be connected in
                    # order to allow merging the subdiagrams.
                    return False

        # Everything OK, the subdiagrams can be merged.
        return True

    # At the very first, we don't know which subdiagrams are
    # commutative, so lets suppose that only trivial one-morphism
    # subdiagrams are.
    commutative_subdiagrams = set(commutative_regions)
    for gen in diagram.expanded_generators:
        if isinstance(gen, CompositeMorphism):
            # Explicitly unpack composites.
            commutative_subdiagrams.add(Diagram(*gen))
        else:
            commutative_subdiagrams.add(Diagram(gen))

    # Now, check all embeddings of all diagrams.
    for commutative_diagram in commutative_diagrams:
        for embedding in diagram_embeddings(commutative_diagram, diagram):
            # All the morphisms to which ``commutative_diagram`` has
            # just been mapped form a commutative subdiagram.
            #
            # Note that, due to transitivity of morphism composition,
            # we are allowed to unroll the composites as shown here.
            new_subdiagram = Diagram(_unroll_composites(embedding.values()))

            if any(new_subdiagram <= subdiagram
                   for subdiagram in commutative_subdiagrams):
                # ``new_commmutative_subset`` is fully absorbed by one
                # of the already found subsets.
                continue

            commutative_subdiagrams.add(new_subdiagram)

            # We will now perform all possible mergers and subsequent
            # absorptions between the commutative subdiagrams.
            more_mergers = True
            while more_mergers:
                more_mergers = False
                new_commutative_subdiagrams = set([])

                # Pick all pairs of subdiagrams and see if they can be
                # merged.
                for (subdiagram1, subdiagram2) in combinations(
                    commutative_subdiagrams, 2):
                    if can_subdiagrams_be_merged(subdiagram1, subdiagram2,
                                                 commutative_subdiagrams):
                        merged_subdiagram = Diagram(subdiagram1.generators +
                                                    subdiagram2.generators)
                        new_commutative_subdiagrams.add(merged_subdiagram)
                        more_mergers = True
                    else:
                        new_commutative_subdiagrams.update([subdiagram1,
                                                            subdiagram2])

                # Remove the diagrams absorbed by other subdiagrams.
                new_commutative_subdiagrams -= set(
                    subdiagram for subdiagram in new_commutative_subdiagrams
                    if any(subdiagram <= absorbing for absorbing
                           in new_commutative_subdiagrams
                           if subdiagram != absorbing))

                commutative_subdiagrams = new_commutative_subdiagrams

                if len(commutative_subdiagrams) == 1:
                    one_subdiagram = iter(commutative_subdiagrams).next()
                    if set(one_subdiagram.generators) == set(
                        diagram.generators):
                        # We have arrived at the conclusion that the whole
                        # ``diagram`` is commutative.
                        return True

    # We have checked everything; ``diagram`` is not commutative.
    return False

def _apply_implication(implication, diagram):
    """
    Generates all possible applications of ``implication`` to
    ``diagram``.  Returns tuples, the first component of which is the
    modified ``diagram``, while the second component is the
    commutative subdiagram which resulted from the application.
    """
    # The general idea is very similar to string rewriting: find all
    # entries of the premise of the implication in ``diagram`` and add
    # the conclusion (or ``implication.diff()``, more exactly).
    conclusion = implication.conclusion
    diff = implication.diff()

    def map_simple_diff_morphism(diff_morphism, object_map):
        """
        Given the non-composite ``diff_morphism`` and an object
        mapping, produces a new morphism in ``diagram`` which would
        match ``diff_morphism``.
        """
        # The first two arguments of any morphism is the domain and
        # the codomain.  This is what we need to change.
        new_domain = object_map[diff_morphism.domain]
        new_codomain = object_map[diff_morphism.codomain]
        the_rest_of_args = diff_morphism.args[2:]
        return diff_morphism.__class__(new_domain, new_codomain,
                                       *the_rest_of_args)

    def map_composite_diff_morphism(diff_composite, simple_morphism_map):
        """
        Given the composite ``diff_composite``, produces the
        corresponding composite in ``diagram``.
        """
        return CompositeMorphism(simple_morphism_map[m] for m in diff_composite)

    # We will store the already modified regions of the diagram in
    # this set and will avoid producing duplicates.  The reason why we
    # may be modifying the same region of ``diagram`` twice is that
    # ``diagram_embeddings`` may yield varied embeddings of morphisms
    # with the same domain and codomain, which will not ultimately
    # affect the result of application.
    registered_regions = set([])

    for premise_embedding in diagram_embeddings(implication.premise, diagram):
        # To know how to add the morphisms in ``diff``, we need to
        # know how the objects of the premise are mapped to the
        # objects of ``diagram``.
        object_map = {}
        for (premise_morphism, diagram_morphism) in premise_embedding.items():
            object_map[premise_morphism.domain] = diagram_morphism.domain
            object_map[premise_morphism.codomain] = diagram_morphism.codomain

        # We will construct the modified diagram from this dictionary.
        new_generators = dict(diagram.generators_properties)

        # We will only explicitly try to add non-composite morphisms.
        # Since the ``implication.conclusion`` is a diagram, this
        # guarantees that ``modified_diagram`` will contain the
        # necessary composites.
        #
        # Yet, we will still need to make sure to get the properties
        # of composites right.  Collect composites on the way, to
        # avoid traversing ``diff`` once again.  Also, remember how
        # simple morphisms are added.
        composites = []
        simple_morphism_map = {}
        for diff_morphism in diff:
            if not isinstance(diff_morphism, CompositeMorphism):
                mapped_morphism = map_simple_diff_morphism(diff_morphism,
                                                           object_map)
                diff_morphism_props = conclusion[diff_morphism]
                simple_morphism_map[diff_morphism] = mapped_morphism

                if mapped_morphism in diagram:
                    # There already is such a morphism in ``diagram``.
                    if diagram[mapped_morphism].subset(diff_morphism_props):
                        # And it actually has all the necessary
                        # properties.
                        continue
                    else:
                        # This morphism doesn't have all the
                        # properties; let's add them.
                        new_generators[mapped_morphism] |= diff_morphism_props
                else:
                    new_generators[mapped_morphism] = diff_morphism_props
            else:
                composites.append(diff_morphism)

        # Now, get the properties of composites right.
        #
        # Before that, we will need to build a provisional version of
        # the modified diagram to be able to easily access the
        # properties of composites.
        modified_diagram = Diagram(new_generators)
        new_generators = dict(modified_diagram.generators_properties)

        # Store how composites are mapped as well.
        composite_map = {}
        for diff_composite in composites:
            diff_composite_properties = conclusion[diff_composite]

            mapped_composite = map_composite_diff_morphism(diff_composite)
            composite_map[diff_composite] = map_composite

            mapped_composite_properties = modified_diagram[mapped_composite]
            if not mapped_composite_properties.subset(diff_composite_properties):
                # We will need to explicitly add some to this
                # composite.
                new_generators[mapped_composite] = mapped_composite_properties | \
                                                   diff_composite_properties

        # Build the final version of the diagram.
        modified_diagram = Diagram(new_generators)

        if modified_diagram != diagram:
            # We have actually changed something, we can yield the
            # modified diagram.  However, we also have to list the
            # affected subdiagram, which is now commutative.
            #
            # The values in the dictionary ``premise_embedding`` are
            # not guaranteed to include all components of all
            # composites, therefore we need to explicitly unroll all
            # composites.  Note that, we can freely do so due to
            # associativity of morphism composition.
            unrolled_morphisms = _unroll_composites(premise_embedding.values())
            affected_subdiagram = Diagram(unrolled_morphisms +
                                          simple_morphism_map.values() +
                                          composite_map.values())

            if affected_subdiagram in registered_regions:
                # We have already yielded this application,
                # essentially.
                continue
            else:
                registered_regions.add(affected_subdiagram)
                yield (modified_diagram, affected_subdiagram)
