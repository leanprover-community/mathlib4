# This file is part of the `polyrith` tactic in `src/tactic/polyrith.lean`.
# It interfaces between Lean and the Sage web interface.

import requests
import json
import sys
from os.path import join, dirname
from subprocess import run
import re

# SINGULAR OPTIONS

# If Singular is installed in the system (in a way that this python process can run,
# that is, in a reachable path), we can try to use it instead of the online sage server
# If Singular is not installed, we can also try to use the version of singular installed inside sage (if sage itself
# is locally installed)

def create_macaulay2_query (type: str, n_vars: int, eq_list, goal_type):
    var_list = ''.join(f"var{i}," for i in range(n_vars)) + 'aux'
    query = f"""
R = QQ[{var_list}];
f = {goal_type};
j,I = ideal({str(eq_list)[1:-1]},1-f*aux);
Gbas = gb(I,ChangeMatrix=>true);
k,Mbas = getChangeMatrix(Gbas);
exponent = max(for i from 0 to (numgens(I)-2) list degree(aux,Mbas_(i,0)));
coeffs = for i from 0 to (numgens(I)-2) list ((Mbas_(i,0)*f^(exponent)) % (I_(numgens(I)-1)));

result = for i from 0 to (length(coeffs)-1) list (
    for j from 0 to (length( terms(coeffs_i) )-1) list (
        {{
            for k from 0 to (numgens(R)-2) list (
                {{k, degree(R_k, (terms(coeffs_i))_j)}}
            ),
            {{numerator coefficient((monomials(coeffs_i))_(0,j),(terms(coeffs_i))_j),
          denominator coefficient((monomials(coeffs_i))_(0,j),(terms(coeffs_i))_j),
            }}
        }}
    )
    );
print(exponent,result);
"""
    return query


def evaluate_in_macaulay2(query: str) -> dict:
    pro = run(["M2", "--silent", "--no-prompts", "-E", "clearEcho stdio"], input=query, capture_output=True, text=True)
    resul = pro.stdout
    if re.match("[a-zA-Z]", resul) or resul.count("(") != 1 or resul.count(")") != 1:
        with open("error","w") as fd:
            fd.write(resul.count("("))
        raise ValueError("Macaulay2 couldn't find a linear combination")
    resul = re.sub("\(([0-9]*),", r"\1;", resul).replace(")","").replace("{","[").replace("}","]").replace(", ]","]")
    return parse_response(resul)

def create_singular_query(type: str, n_vars: int, eq_list, goal_type):
    var_list = ''.join(f"var{i}," for i in range(n_vars)) + 'aux'
    query = f"""
LIB "elim.lib";
ring r = 0,({var_list}),dp;
poly p = {goal_type};
ideal I = {str(eq_list)[1:-1]},1-p*aux;
ideal result = lift(I,1);
int i,j,k;
poly h;
int powr=0;
for (i=1; i<= size(result); i++)
{{
    h = 0+1*result[i];
    for (j=1;j<=size(result[i]);j++)
    {{
        powr = max(powr, leadexp(h)[nvars(basering)]);
        h = h - lead(h);
    }}
}}

print(powr);
print(";");

list coefs;
for (i=1;i<size(result);i++){{
    coefs=insert(coefs,reduce(result[i]*p^powr,1-aux*p),size(coefs));
}}

proc imprime(poly f)
{{
    poly g = f;
    for (int i=1;i<=size(f); i++)
    {{
        print("[[");
        for (k=1;k<nvars(basering);k++)
            {{
            if (leadexp(g)[k] != 0) {{
                print("[");
                print(k-1);
                print(",");
                print(leadexp(g)[k]);
                print("],");
                }}
            }}
        print("],");
        print("[");
        print(numerator(leadcoef(g)));
        print(",");
        print(denominator(leadcoef(g)));
        print("]],");
        g = g - lead(g);
    }}
}}

print("[");
for (int a=1;a<=size(coefs);a++)
{{
    print("[");
    imprime(coefs[a]);
    print("],");
}}
print("]");
quit;
    """
    return query

def evaluate_in_singular(query: str) -> dict:
    try:
        pro = run(["Singular", "-q"], input=query, capture_output=True, text=True)
    except:
        pro = run(["sage", "-ingular", "-q"], input=query, capture_output=True, text=True)
    resul = pro.stdout
    if re.match("[a-zA-Z]", resul) or resul.count(";") != 1:
        raise ValueError("Singular couldn't find a linear combination")
    resul = resul.replace("\n","").replace(",]","]").replace(",",", ")
    return parse_response(resul)


# These functions are used to format the output of Sage for parsing in Lean.
# They are stored here as a string since they are passed to Sage via the web API.
with open(join(dirname(__file__), "polyrith_sage_helper.py"), encoding='utf8') as f:
    polynomial_formatting_functions = f.read()

# future extensions may change behavior depending on the base type
def type_str(type):
    return "QQ"

def create_query(type: str, n_vars: int, eq_list, goal_type):
    """ Create a query to invoke Sage's `MPolynomial_libsingular.lift`. See
    https://github.com/sagemath/sage/blob/f8df80820dc7321dc9b18c9644c3b8315999670b/src/sage/rings/polynomial/multi_polynomial_libsingular.pyx#L4472-L4518
    for a description of this method. """
    var_list = [f"var{i}" for i in range(n_vars)] + ['aux']
    query = f'''
if {n_vars!r} != 0:
    P = PolynomialRing({type_str(type)}, {var_list})
    [{", ".join(var_list)}] = P.gens()
    p = P({goal_type})
    gens = {eq_list} + [1 - p*aux]
    I = P.ideal(gens)
    coeffs = P(1).lift(I)
    power = max(cf.degree(aux) for cf in coeffs)
    coeffs = [P(cf.subs(aux = 1/p)*p^power) for cf in coeffs[:int(-1)]]
    print(str(power)+';'+serialize_polynomials(coeffs))
else:
    # workaround for a Sage shortcoming with `n_vars = 0`,
    # `TypeError: no conversion of this ring to a Singular ring defined`
    # In this case, there is no need to look for membership in the *radical*;
    # we just check for membership in the ideal, and return exponent 1
    # if coefficients are found.
    P = PolynomialRing({type_str(type)}, 'var', 1)
    p = P({goal_type})
    I = P.ideal({eq_list})
    coeffs = p.lift(I)
    print('1;'+serialize_polynomials(coeffs))
'''
    return query

class EvaluationError(Exception):
    def __init__(self, ename, evalue, message='Error in Sage communication'):
        self.ename = ename
        self.evalue = evalue
        self.message = message
        super().__init__(self.message)

def parse_response(resp: str) -> str:
    exp, data = resp.split(';', 1)
    return dict(power=int(exp), coeffs=json.loads(data))


def evaluate_in_sage(query: str) -> str:
    data = {'code': query}
    headers = {'content-type': 'application/x-www-form-urlencoded'}
    response = requests.post('https://sagecell.sagemath.org/service', data, headers=headers).json()
    if response['success']:
        return parse_response(response.get('stdout'))
    elif 'execute_reply' in response and 'ename' in response['execute_reply'] and 'evalue' in response['execute_reply']:
        raise EvaluationError(response['execute_reply']['ename'], response['execute_reply']['evalue'])
    else:
        raise Exception(response)

def main():
    '''The system args contain the following:
    0 - the path to this python file
    1 - a string containing "true" or "false" depending on whether polyrith was called with trace enabled
    2 - a string representing the base type of the target
    3 - the number of variables used
    4 - a list of the polynomial hypotheses/proof terms in terms of the variables
    5 - a single polynomial representing the target

    This returns a json object with format:
    ```
    { success: bool,
      data: Optional[list[str]],
      trace: Optional[str],
      name: Optional[str],
      value: Optional[str] }
    ```
    '''
    try:
        command = create_singular_query(sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5])
        output = dict(success=True, data=evaluate_in_singular(command))
    except:
        try:
            command = create_macaulay2_query(sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5])
            output = dict(success=True, data=evaluate_in_macaulay2(command))
        except:
            command = create_query(sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5])
            final_query = polynomial_formatting_functions + "\n" + command
            if sys.argv[1] == 'true': # trace dry run enabled
                output = dict(success=True, trace=command)
            else:
                try:
                    output = dict(success=True, data=evaluate_in_sage(final_query))
                except EvaluationError as e:
                    output = dict(success=False, name=e.ename, value=e.evalue)
    print(json.dumps(output))

if __name__ == "__main__":
    main()
