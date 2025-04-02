from pyeda.inter import expr
from pyeda.boolalg.minimization import espresso_exprs
from pyeda.boolalg.expr import OrOp, AndOp, Complement, Variable
import argparse

def clause_to_str(clause):
    """Convert a PyEDA clause to string representation"""
    if isinstance(clause, AndOp):
        return " & ".join(str(lit) for lit in clause.xs)
    elif isinstance(clause, (Variable, Complement)):
        return str(clause)
    else:
        return str(clause)  # fallback

def espresso_minimize(formula_str):
    """Minimize using Espresso and return standard DNF format"""
    expr_formula = expr(formula_str, simplify=True)
    if not expr_formula.is_dnf():
        expr_formula = expr_formula.to_dnf()
    minimized = espresso_exprs(expr_formula.to_dnf())[0]
    
    # Convert to standard DNF format
    if isinstance(minimized, OrOp):
        clauses = []
        for clause in minimized.xs:
            clause_str = clause_to_str(clause)
            if " & " in clause_str or isinstance(clause, AndOp):
                clauses.append(f"({clause_str})")
            else:
                clauses.append(clause_str)
        return " | ".join(clauses)
    else:
        # Single clause case
        clause_str = clause_to_str(minimized)
        return f"({clause_str})" if " & " in clause_str else clause_str

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", help="Input Boolean formula file")
    parser.add_argument("output_file", help="Output DNF file")
    args = parser.parse_args()

    with open(args.input_file, 'r') as f:
        formula_str = f.read().strip()
    
    dnf = espresso_minimize(formula_str)
    
    with open(args.output_file, 'w') as f:
        f.write(dnf)