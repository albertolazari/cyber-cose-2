import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser 
from collections import deque

specTypes = {'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF, 'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR,
    'AND': parser.AND, 'NOT': parser.NOT, 'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT,

    'NEXT': parser.OP_NEXT, 'OP_GLOBAL': parser.OP_GLOBAL, 'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL, 'NOTEQUAL': parser.NOTEQUAL, 'LT': parser.LT, 'GT': parser.GT,
    'LE': parser.LE, 'GE': parser.GE, 'TRUE': parser.TRUEEXP, 'FALSE': parser.FALSEEXP
}

basicTypes = {parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
              parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE}
booleanOp = {parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF}

def spec_to_bdd(model, spec):
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec

def is_boolean_formula(spec):
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators. 
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False
    
def check_GF_formula(spec):
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a 
    boolean combination of base formulas with no temporal operators.
    Returns the formula f if `spec` is in the correct form, None otherwise 
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
        return False
    if is_boolean_formula(spec.car):
        return spec.car
    else:
        return None

def parse_react(spec):
    """
    Visit the syntactic tree of the formula `spec` to check if it is a reactive formula,
    that is wether the formula is of the form
    
                    GF f -> GF g
    
    where f and g are boolean combination of basic formulas.
    
    If `spec` is a reactive formula, the result is a pair where the first element is the 
    formula f and the second element is the formula g. If `spec` is not a reactive 
    formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
        return None
    # Check if lhs of the implication is a GF formula
    f_formula = check_GF_formula(spec.car)
    if f_formula == None:
        return None
    # Create the rhs of the implication is a GF formula
    g_formula = check_GF_formula(spec.cdr)
    if g_formula == None:
        return None
    return (f_formula, g_formula)

def find_reach(Init):
    model = pynusmv.glob.prop_database().master.bddFsm

    New = Init
    Reach = Init
    while not New.is_false():
        New = model.post(New) - Reach
        Reach = Reach + New
    return Reach

def create_trace(model, loop_trace):
    return None

    

def check_react_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. 
    """

    model = pynusmv.glob.prop_database().master.bddFsm
    res = parse_react(spec)
    if res == None:
        return None
    F = spec_to_bdd(model, res[0])
    G = spec_to_bdd(model, res[1])

    Reach = find_reach(model.init)                            # trovare reach
    F = (F & Reach) - G

    '''
    Recur := Intersect(Reach, F) // Potential candidates for cycle
    while not IsEmpty(Recur) do // Iterate on Recur_i
        PreReach := empty // States that can reach Recur_i in ≥ 1 steps
        New := Pre(Recur, Trans) // Ensure at least one transition
        while not IsEmpty(New) do
            PreReach := Union(PreReach, New)
            if IsSubset(Recur, PreReach) then
                return True // Recur won't change: F repeatable
            end if
            New := Diff(Diff(Pre(New, Trans), PreReach), G)
        end while
        Recur := Intersect(Recur, PreReach) // Recur_i+1
    end while
    return False // No execution with F repeating
    '''

    # a + b and a | b compute the disjunction of a and b
    # a * b and a & b compute the conjunction of a and b
    # ~a and -a compute the negation of a
    # a - b computes a & ~b
    # a ^ b computes the exclusive-OR (XOR) of a and b
    # a == b, a <= b, a < b, a > b and a >= b compare a and b

    Recur = F                               # Potential candidates for cycle
    while not Recur.is_false():             # Iterate on Recur_i
        # This is what we would like to do
        PreReach = pynusmv.dd.BDD.false()   # States that can reach Recur_i in ≥ 1 steps
 
        New = model.pre(Recur) - G              # Ensure at least one transition
        loop_trace = [New]
 
        while not New.is_false():
            PreReach = PreReach | New
            # assert ((Recur <= PreReach) == Recur.entailed(PreReach))
            # assert ((Recur <= PreReach) == ((Recur & PreReach) == Recur))
            if Recur <= PreReach:
                return False, create_trace(model, loop_trace)                 # Recur won't change: F repeatable
 
            New = (model.pre(New) - G) - PreReach
            loop_trace.append(New)
        
        Recur = Recur & PreReach # Recur_i+1
    
    return True, None # No execution with F repeating

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
type_ltl = pynusmv.prop.propTypes['LTL']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    print(spec)
    if prop.type != type_ltl:
        print("property is not LTLSPEC, skipping")
        continue
    res = check_react_spec(spec)
    if res == None:
        print('Property is not a GR(1) formula, skipping')
    if res[0] == True:
        print("Property is respected")
    elif res[0] == False:
        print("Property is not respected")
        print("Counterexample:", res[1])

pynusmv.init.deinit_nusmv()