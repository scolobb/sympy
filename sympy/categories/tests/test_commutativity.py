from sympy.categories import (Object, NamedMorphism, IdentityMorphism,
                              Diagram)
from sympy.categories import diagram_embeddings
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
