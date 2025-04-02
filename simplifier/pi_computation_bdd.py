from dd import autoref as _bdd
import re

def ite_to_formula(ite_expr):
    """Convert ITE expression to standard logical formula"""
    # Base cases
    if ite_expr == "TRUE":
        return "TRUE"
    if ite_expr == "FALSE":
        return "FALSE"
    
    # Match ITE pattern
    match = re.match(r'ite\(([^,]+),\s*([^,]+),\s*([^)]+)\)', ite_expr)
    if not match:
        return ite_expr  # not an ITE expression
    
    var, then_branch, else_branch = match.groups()
    
    # Recursively convert branches
    then_part = ite_to_formula(then_branch)
    else_part = ite_to_formula(else_branch)
    
    # Build the formula
    return f"({var} ∧ {then_part}) ∨ (¬{var} ∧ {else_part})"

def simplify_formula(formula):
    """Apply basic simplifications"""
    simplifications = [
        (r'\(([^()]+) ∧ TRUE\)', r'\1'),
        (r'\(TRUE ∧ ([^()]+)\)', r'\1'),
        (r'\(([^()]+) ∨ FALSE\)', r'\1'),
        (r'\(FALSE ∨ ([^()]+)\)', r'\1'),
        (r'¬TRUE', 'FALSE'),
        (r'¬FALSE', 'TRUE'),
        (r'\(([^()]+) ∧ FALSE\)', 'FALSE'),
        (r'\(FALSE ∧ ([^()]+)\)', 'FALSE')
    ]
    
    for pattern, replacement in simplifications:
        formula = re.sub(pattern, replacement, formula)
    
    return formula

# Create BDD manager
bdd = _bdd.BDD()

# Declare variables in order (important for consistent behavior)

bdd.declare('a')
bdd.declare('b')
bdd.declare('c')
bdd.declare('d')
bdd.declare('e')
bdd.declare('f')
bdd.declare('g')
bdd.declare('h')
bdd.declare('i')
bdd.declare('j')
bdd.declare('k')

# Build the BDD for (a & (b | a))
formula = r"(a & b) | (c & d & e) | (f & g) | (h & i) | (j & k) | (~a)"
#formula = r'(a & (b | c))'
u = bdd.add_expr(formula)

# Get prime implicants
#prime_implicants = get_prime_implicants(bdd, u)

# Format and print
#print("Prime implicants:", format_prime_implicants(prime_implicants))
#print("Prime implicants (minimal expresion:", bdd.to_expr(u))
ite_expr = bdd.to_expr(u)

standard_form = ite_to_formula(ite_expr)
simplified_form = simplify_formula(standard_form)

print("ITE Expression:", ite_expr)
print("Standard Form:", standard_form)
print("Simplified Form:", simplified_form)