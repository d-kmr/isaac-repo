from sympy import sympify, to_cnf;
with open('input.bool') as f: expr = f.read().strip();
verilog = to_cnf(sympify(expr))
with open('input.v', 'w') as f: f.write(f'module formula(output x); assign x = {verilog}; endmodule')