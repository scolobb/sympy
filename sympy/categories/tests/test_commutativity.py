from sympy.categories import (Object, NamedMorphism, IdentityMorphism,
                              Diagram, Implication)
from sympy.categories import diagram_embeddings
from sympy.categories.commutativity import (_check_commutativity_with_diagrams,
                                            _apply_implication)
from sympy import Dict

def test_diagram_embeddings():
    A = Object("A")
    B = Object("B")
    C = Object("C")
    D = Object("D")
    f = NamedMorphism(A, B, "f")
    g = NamedMorphism(B, D, "g")
    h = NamedMorphism(A, C, "h")
    k = NamedMorphism(C, D, "k")

    id_A = IdentityMorphism(A)
    id_B = IdentityMorphism(B)
    id_C = IdentityMorphism(C)
    id_D = IdentityMorphism(D)

    # Test the embeddings of a triangle into a square.
    tri = Diagram(f, g)
    square = Diagram(f, g, h, k)

    embeddings = set([
        Dict({f: f, g: g, g * f: g * f, id_A: id_A, id_B: id_B, id_D: id_D}),
        Dict({f: h, g: k, g * f: k * h, id_A: id_A, id_B: id_C, id_D: id_D}),
        ])

    assert set(diagram_embeddings(tri, square)) == embeddings

    # Test how properties are preserved while constructing the
    # embeddings of a triangle into a square,
    tri = Diagram({f: "golden", g: "silver"})
    square = Diagram({f: [], g: [], h: "golden", k: "silver"})

    embeddings = set([
        Dict({f: h, g: k, g * f: k * h, id_A: id_A, id_B: id_C, id_D: id_D}),
        ])

    assert set(diagram_embeddings(tri, square)) == embeddings

    # Test explicit properties on composite morphisms.
    tri1 = Diagram({f: "golden", g: "golden"})
    tri2 = Diagram({f: "golden", g: "golden", g * f: ["wooden"]})
    assert set(diagram_embeddings(tri1, tri2)) == set([])
    assert set(diagram_embeddings(tri2, tri1)) == set([])

    # Test the embeddings of the square into itself.
    embeddings = set([
        Dict({f: f, g: g, h: h, k: k, g * f: g * f, k * h: k * h,
              id_A: id_A, id_B: id_B, id_C: id_C, id_D: id_D})
        ])

    assert set(diagram_embeddings(square, square)) == embeddings

    # Test the embeddings of a simple diagram in a cube diagram.

    # A simple diagram.
    A = Object("A")
    B = Object("B")
    C = Object("C")
    D = Object("D")
    f = NamedMorphism(A, B, "f")
    g = NamedMorphism(B, C, "g")
    h = NamedMorphism(D, A, "h")
    k = NamedMorphism(D, B, "k")
    simple = Diagram({f: [], g: "fuel", h: "rabbit", k: []})

    # A cube.
    A1 = Object("A1")
    A2 = Object("A2")
    A3 = Object("A3")
    A4 = Object("A4")
    A5 = Object("A5")
    A6 = Object("A6")
    A7 = Object("A7")
    A8 = Object("A8")
    id_A1 = IdentityMorphism(A1)
    id_A2 = IdentityMorphism(A2)
    id_A3 = IdentityMorphism(A3)
    id_A4 = IdentityMorphism(A4)
    id_A5 = IdentityMorphism(A5)
    id_A6 = IdentityMorphism(A6)
    id_A7 = IdentityMorphism(A7)
    id_A8 = IdentityMorphism(A8)

    # The top face of the cube.
    f1 = NamedMorphism(A1, A2, "f1")
    f2 = NamedMorphism(A1, A3, "f2")
    f3 = NamedMorphism(A2, A4, "f3")
    f4 = NamedMorphism(A3, A4, "f3")

    # The bottom face of the cube.
    f5 = NamedMorphism(A5, A6, "f5")
    f6 = NamedMorphism(A5, A7, "f6")
    f7 = NamedMorphism(A6, A8, "f7")
    f8 = NamedMorphism(A7, A8, "f8")

    # The remaining morphisms.
    f9 = NamedMorphism(A1, A5, "f9")
    f10 = NamedMorphism(A2, A6, "f10")
    f11 = NamedMorphism(A3, A7, "f11")
    f12 = NamedMorphism(A4, A8, "f11")

    cube = Diagram({f1: [], f2: [], f3: [], f4: "rabbit", f5: [], f6: [],
                    f7: "fuel", f8: [], f9: [], f10: [], f11: [], f12: []})
    assert set(diagram_embeddings(simple, cube)) == set([])

    cube = Diagram({f1: "rabbit", f2: [], f3: [], f4: [], f5: [], f6: [],
                    f7: "fuel", f8: [], f9: [], f10: [], f11: [], f12: []})

    embeddings = set([
        Dict({g * f: f7 * f10, f * h: f10 * f1, g * k: f7 * f10 * f1,
              g * f * h: f7 * f10 * f1, id_A: id_A2, id_B: id_A6, id_C: id_A8,
              id_D: id_A1, f: f10, g: f7, h: f1, k: f10 * f1}),
        Dict({g * f: f7 * f10, f * h: f10 * f1, g * k: f7 * f5 * f9,
              g * f * h: f7 * f10 * f1, id_A: id_A2, id_B: id_A6,
              id_C: id_A8, id_D: id_A1, f: f10, g: f7, h: f1, k: f5 * f9})
        ])

    assert set(diagram_embeddings(simple, cube)) == embeddings

    # Reset the objects and the morphisms for infinite-case tests.
    #
    # Since with loops there so many embeddings, we will sometimes
    # only count them.  This is not a bit problem, eventually, since
    # some cases will get tested thoroughly.

    A = Object("A")
    B = Object("B")
    C = Object("C")
    D = Object("D")
    f = NamedMorphism(A, B, "f")
    g = NamedMorphism(B, D, "g")
    h = NamedMorphism(A, C, "h")
    k = NamedMorphism(C, D, "k")

    id_A = IdentityMorphism(A)
    id_B = IdentityMorphism(B)
    id_C = IdentityMorphism(C)
    id_D = IdentityMorphism(D)

    # Test the embeddings of a triangle into a square cycle.
    tri = Diagram(f, g)
    h = NamedMorphism(C, A, "h")
    k = NamedMorphism(D, C, "k")
    square_cycle = Diagram(f, g, h, k)

    assert len(list(diagram_embeddings(tri, square_cycle))) == 768

    tri = Diagram({f: "golden", g: "silver"})
    square_cycle = Diagram({f: "silver", g: [], h: "golden", k: []})

    embeddings = set([
        Dict({g * f: f * h, id_A: id_C, id_B: id_A, id_D: id_B, f: h, g: f}),
        Dict({g * f: f * h, id_A: k * g * f * h, id_B: id_A, id_D: id_B, f: h,g: f}),
        Dict({g * f: f * h, id_A: id_C, id_B: id_A, id_D: f * h * k * g, f: h, g: f}),
        Dict({g * f: f * h, id_A: k * g * f * h, id_B: id_A, id_D: f * h * k * g, f: h, g: f}),
        Dict({g * f: f * h, id_A: id_C, id_B: h * k * g * f, id_D: id_B, f: h, g: f}),
        Dict({g * f: f * h, id_A: k * g * f * h, id_B: h * k * g * f, id_D: id_B, f: h, g: f}),
        Dict({g * f: f * h, id_A: id_C, id_B: h * k * g * f, id_D: f * h * k * g, f: h, g: f}),
        Dict({g * f: f * h, id_A: k * g * f * h, id_B: h * k * g * f, id_D: f * h * k * g, f: h, g: f})
        ])

    assert set(diagram_embeddings(tri, square_cycle)) == embeddings

    # Test the embeddings of triangular cycle into a square cycle.
    m = NamedMorphism(D, A, "m")
    tri_cycle = Diagram({f: "golden", g: "silver", m: []})

    assert len(list(diagram_embeddings(tri_cycle, square_cycle))) == 16

    # Test the embeddings of two-element cycle into a triangular cycle.
    f = NamedMorphism(A, B, "f")
    g = NamedMorphism(B, A, "g")
    pattern = Diagram(f, g)

    h = NamedMorphism(B, C, "h")
    k = NamedMorphism(C, A, "k")
    model = Diagram(f, g, k)

    # from sympy import pprint
    # print
    # for embedding in diagram_embeddings(pattern, model):
    #     pprint(embedding, use_unicode=False)

    assert len(list(diagram_embeddings(pattern, model))) == 32

    # Test the embeddings of the two-element cycle into two triangular
    # cycles connected with a two morphisms.
    E = Object("E")
    F = Object("F")
    m = NamedMorphism(D, E, "m")
    n = NamedMorphism(E, F, "n")
    p = NamedMorphism(F, D, "p")
    u = NamedMorphism(A, E, "u")
    v = NamedMorphism(C, D, "v")
    model = Diagram(f, h, k, m, n, p, u, v)

    assert len(list(diagram_embeddings(pattern, model))) == 192

    # Test the embeddings of two two-element cycles connected with two
    # components into itself.

    h = NamedMorphism(C, D, "h")
    k = NamedMorphism(D, C, "k")
    u = NamedMorphism(A, C, "u")
    v = NamedMorphism(B, D, "v")
    model = Diagram(f, g, h, k, u, v)

    embeddings_list = list(diagram_embeddings(pattern, model))
    embeddings = set(embeddings_list)
    assert len(embeddings_list) == 64
    assert len(embeddings) == 64

    assert Dict({g * f: g * f, f * g: f * g, f * g * f: f * g * f,
                 g * f * g: g * f * g, id_A: id_A,
                 id_B: id_B, f: f, g: g}) in embeddings

    assert Dict({g * f: k * h * k * h * k * h, f * g: h * k * h * k * h * k,
                 f * g * f: h * k * h * k * h * k * h * k * h,
                 g * f * g: k * h * k * h * k * h * k * h * k,
                 id_A: id_C, id_B: id_D, f: h * k * h, g: k * h * k}) in embeddings
    assert Dict({g * f: g * f * g * f, f * g: f * g * f * g,
                 f * g * f: f * g * f * g * f, g * f * g: g * f * g * f * g * f * g,
                 id_A: g * f, id_B: id_B, f: f, g: g * f * g}) in embeddings
    assert Dict({g * f: k * h * k * h, f * g: h * k * h * k,
                 f * g * f: h * k * h * k * h * k * h,
                 g * f * g: k * h * k * h * k, id_A: k * h,id_B: id_D,
                 f: h * k * h, g: k}) in embeddings

def test_check_commutativity_with_diagrams():
    # We will a check a partial formulation of a simple theorem
    # related to zero objects.
    A = Object("A")
    B = Object("B")
    X = Object("X")
    Y = Object("Y")
    Z = Object("Z")
    id_Z = IdentityMorphism(Z)

    # First, define a zero object.  A zero object is an object which
    # is final _and_ initial.

    # `Z` is a final object if for any object `X` there exists exactly
    # one morphism `X\rightarrow Z`.  The uniqueness part of this can
    # also be stated as "any two morphisms `f_1:X\rightarrow Z` and
    # `f_2:X\rightarrow Z` are equal".
    f1 = NamedMorphism(X, Z, "f1")
    f2 = NamedMorphism(X, Z, "f2")
    final_object = Diagram({f1: [], f2: [], id_Z: "zero"})

    # `Z` is an initial object if for any object `Y` there exists
    # exactly one morphism `Z\rightarrow Y`.  The uniqueness part of
    # this statement can be formulated as "any two morphisms
    # `g_1:Z\rightarrow Y` and `g_2:Z\rightarrow Y` are equal".
    g1 = NamedMorphism(Z, Y, "g1")
    g2 = NamedMorphism(Z, Y, "g2")
    initial_object = Diagram({g1: [], g2: [], id_Z: "zero"})

    # Now, our simple theorem.  Consider two arbitrary objects `A` and
    # `B`, a zero object `Z`, and the morphisms `h_1:A\rightarrow Z`,
    # `k_1:Z\rightarrow B`, `h_2:A\rightarrow Z`, and
    # `k_2:Z\rightarrow B`.  Then `k_1\circ h_1 = k_2\circ h_2`.
    #
    h1 = NamedMorphism(A, Z, "h1")
    k1 = NamedMorphism(Z, B, "k1")
    h2 = NamedMorphism(A, Z, "h2")
    k2 = NamedMorphism(Z, B, "k2")
    theorem = Diagram({h1: [], k1: [], h2: [], k2: [],
                       id_Z: "zero"})

    assert _check_commutativity_with_diagrams(
        theorem, [final_object, initial_object])

def test_apply_implication():
    A = Object("A")
    B = Object("B")
    C = Object("C")
    D = Object("D")

    f = NamedMorphism(A, B, "f")
    g = NamedMorphism(B, C, "g")
    h = NamedMorphism(C, A, "h")

    k1 = NamedMorphism(A, B, "k1")
    m1 = NamedMorphism(B, D, "m1")
    k2 = NamedMorphism(A, C, "k2")
    m2 = NamedMorphism(C, D, "m2")

    h1 = NamedMorphism(D, A, "h")

    # This implication has no actual meaning.
    imp = Implication(Diagram(f, g), Diagram({h: "bear"}))

    # Test the application of a simple implication to a square
    # diagram.
    square = Diagram(k1, m1, k2, m2)
    results = set([
        (Diagram({k1: [], m1: [], k2: [], m2: [], h1: "bear"}),
         Diagram(k1, m1, h1)),
        (Diagram({k1: [], m1: [], k2: [], m2: [], h1: "bear"}),
         Diagram(k2, m2, h1)),
        ])
    assert set(_apply_implication(imp, square)) == results

    # Test the application of the implication to a square diagram
    # which already has one morphism `h:D\rightarrow A` with the
    # property "bear".
    imp = Implication(Diagram({f: "anchor1", g: "anchor2"}), Diagram({h: "bear"}))
    square = Diagram({k1: "anchor1", m1: "anchor2", k2: [], m2: [], h1: "bear"})
    assert set(_apply_implication(imp, square)) == set([])

    # Test the application of the implication to a square diagram
    # which already has one morphism `h:D\rightarrow A` with some
    # other property.
    square = Diagram({k1: "anchor1", m1: "anchor2", k2: [], m2: [], h1: "plesiosaur"})
    results = set([
        (Diagram({k1: "anchor1", m1: "anchor2", k2: [], m2: [], h1: ["bear", "plesiosaur"]}),
         Diagram(k1, m1, h1)),
        (Diagram({k1: "anchor1", m1: "anchor2", k2: [], m2: [], h1: ["bear", "plesiosaur"]}),
         Diagram(k1, m1, h1, k2, m2))
        ])
    assert set(_apply_implication(imp, square)) == results
