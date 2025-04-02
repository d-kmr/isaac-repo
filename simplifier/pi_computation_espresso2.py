from pyeda.inter import expr, espresso_exprs

def find_prime_implicants(formula: str):

    # Convert the formula string to an expression object
    boolean_expr = expr(formula)
    
    minimized, = espresso_exprs(boolean_expr)

    return minimized

# Example with a non-DNF formula
formula = "(a & b) | (c & d & e) | (f & g) | (h & i) | (j & k) | (~a)"
print("Original Formula:", formula)
print("Prime Implicants:", find_prime_implicants(formula))
