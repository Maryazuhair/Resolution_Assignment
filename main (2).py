# formula: ∀x(P(x)⇒Q(x)) ∧ ¬ ∨ ∃
couneter = 97
def add_char_at_position(original_string, position,char_to_add):
    return original_string[:position] + char_to_add + original_string[position:]
def remove_char_at_position(original_string, position):
    return original_string[:position] + original_string[position + 1:]
def replace_char_at_index(string, index, new_char):
    return string[:index] + new_char + string[index + 1:]
def eliminate_implication(formula):
    for i in range(len(formula)):
        if formula[i] == '⇒':
            formula = replace_char_at_index(formula,i,"∨")
            for j in range(i-1,-1,-1):
                if formula[j]=='(':
                    formula = replace_char_at_index(formula, j-1, "¬"+formula[j-1])
                    break
    return formula

def move_negation_inward(formula):
    #not complete
    start = 0
    end = 0
    string = ""
    for i in range(len(formula)):
        if formula[i] == '¬' and formula[i + 1] == '∃':
            formula =  remove_char_at_position(formula,i)
            formula =  replace_char_at_index(formula, i, '∀')
            formula =  add_char_at_position(formula, i+2, '¬')
        elif formula[i] == '¬' and formula[i + 1] == '∀':
            formula = replace_char_at_index(formula, i, '∃')
            formula = replace_char_at_index(formula, i+1, '¬')
        if formula[i] == '¬' and formula[i + 1] == '(':
            start = i + 1
            for j in range(i, len(formula)):
                if formula[j] == ')' and formula[j + 1] == ')' and (j + 2 == len(formula) or formula[j + 2] == '∧' or formula[j + 2] == '∨'):
                    end = j+2
                    break

            formula = remove_char_at_position(formula, start-1)
            #(¬Q(x,y)∧Q(y,x))
            while start != end:
                if ord(formula[start]) >= 65 and ord(formula[start]) <= 90:

                    formula = add_char_at_position(formula, start, '¬')
                    start = start + 1
                elif formula[start] == "¬":
                        formula = add_char_at_position(formula, start,'¬')
                        start = start + 2
                elif formula[start] == "∨":
                    formula = replace_char_at_index(formula, start, '∧')

                elif formula[start] == "∧":
                    formula = replace_char_at_index(formula, start, '∨')
                start+=1
    return formula



#
def remove_double_not(formula):
    start = 0
    end = len(formula)
    while start != end:
        if formula[start] == '¬' and formula[start+1] == '¬':
            formula = remove_char_at_position(formula, start)
            formula = remove_char_at_position(formula, start)
            end-=2
        start+=1
    return formula




def standardize_variable_scope(formula):
    global couneter
    for i in range(len(formula)):
        if formula[i] == '∀':
            for j in range(i+2,len(formula)):
                if(formula[i+1] == formula[j] and formula[j -1] == '∀'):
                    couneter += 1
                    if couneter == 99 or couneter == 102:
                        couneter += 1
                    char = formula[i+1]
                    formula = replace_char_at_index(formula, i+1, chr(couneter))
                    for k in range(i+2, len(formula)):
                        if (char == formula[k]):
                            formula = replace_char_at_index(formula, k, chr(couneter))
                        if (formula[k] == '∀' or formula[k] == '∃'):
                            break
                    break
    return formula

#
def prenex_form(formula):
    new = ""
    str = formula
    for i in range(len(formula)):
        if (formula[i] == '∀') and (i != 0):
            new += formula[i] + formula[i+1]
            str = str.replace("∀"+formula[i+1], "")
    formula = new + str
    return formula

def skolemization(formula):
    global couneter
    start = 0
    end = len(formula)
    while start != end:
        if (formula[start] == '∃'):
            char = formula[start + 1]
            formula = remove_char_at_position(formula, start)
            formula = remove_char_at_position(formula, start)
            for k in range(start+1,len(formula)):
                if ( char== formula[k]):
                    formula = replace_char_at_index(formula, k, "f(x)")
                if(formula[k] == '∀' or formula[k] == '∃'):
                    break
            end-=2
        start += 1
    return formula



def eliminate_universal_quantifiers(formula):
    count = 0
    for i in range(len(formula)):
        if(formula[i] == '∀'):
            count += 1
    for i in range(count):
        formula = replace_char_at_index(formula, formula.index("∀")+1, '')
        formula = replace_char_at_index(formula, formula.index("∀"), '')
    return formula

#
def convert_to_cnf(formula):
    str = ""
    result = ""
    for i in range(len(formula)):
        if(formula[i] == '∨' and formula[i+1] == '('):
            for m in range(i - 1, -1, -1):
                if (ord(formula[m]) >= 65 and ord(formula[m]) <=  90):
                    if(formula[m-1] == '('):
                        add = formula[m:i]
                    else:
                        add = formula[m - 1:i]

            for k in range(i+1,len(formula)):
                if formula[k] == '∧':
                    for j in range(k - 1, -1, -1):
                        if (ord(formula[j]) >= 65 and ord(formula[j]) <=  90) and (formula[j-1] == '∨'or formula[j-2] == '∨'):
                            for r in range(j - 2, -1, -1):
                                if ord(formula[r]) >= 65 and ord(formula[r]) <=  90:
                                    str = add + "∨" + formula[r:k]
                                    result += str + '\n' + "∧"
                                    break
                            break
                        elif ord(formula[j]) >= 65 and ord(formula[j]) <=  90:
                            str = "(" + add +"∨"+ formula[j:k] + ")"
                            result += str  + '\n' + "∧"

                            break
            for n in range(len(formula) - 1 , -1, -1):
                if(formula[n] == '∧'):
                    str = add + "∨" + formula[n+1:len(formula)]
                    result += str + '\n'

                    break
    return result





def turn_conjunctions_into_clauses(formula):
    start = 0
    end = len(formula)
    while start != end:
        if (formula[start] == '∧'):
            formula = remove_char_at_position(formula, start)
            end -= 1
        start += 1
    return formula


def rename_variables_in_clauses(formula):
    global couneter
    for i in range(len(formula)):
        if ord(formula[i]) >= 65 and ord(formula[i]) <= 90:
            char = formula[i+2]
            for k in range(i+3,len(formula)):
                if(formula[k] == "∧"):
                    couneter += 1
                    for l in range(k,len(formula)):
                        if(formula[l] == "\n"):
                            break
                        elif(formula[l] == char):
                            formula = replace_char_at_index(formula, l, chr(couneter))


                    # while formula[count] != "\n":
                    #     str += "ho"+formula[count]
                    #     # if char == formula[count]:
                    #     #     formula = replace_char_at_index(formula, k, chr(couneter))
                    #     count+=1
                    # str += "one"
            break
    return formula
#
#
#             break



# Example usage:
# formula: 
formula = '∀x(B(x)⇒(∃y(Q(x,y)∧¬P(y))∧¬∃y(Q(x,y)∧Q(y,x))∧∀y(¬B(y)⇒¬E(x,y))))'
print("Original Formula:", formula)
print("\n")
formula = eliminate_implication(formula)
print("After Eliminating Implication:", formula)
print("\n")

formula = move_negation_inward(formula)
print("After Moving Negation Inward:", formula)
print("\n")

#
formula = remove_double_not(formula)
print("After Removing Double Negation:", formula)
#
print("\n")

formula = skolemization(formula)
print("After Skolemization:", formula)
#
print("\n")

formula = standardize_variable_scope(formula)
print("After Standardizing Variable Scope:", formula)
print("\n")

formula = prenex_form(formula)
print("After Prenex Form:", formula)
#
print("\n")

#
formula = eliminate_universal_quantifiers(formula)
print("After Eliminating Universal Quantifiers:", formula)
#
print("\n")

formula = convert_to_cnf(formula)
print("After Conversion to CNF:", formula)
#
print("\n")

formula = rename_variables_in_clauses(formula)
print("After renaming variables:", formula)
formula = turn_conjunctions_into_clauses(formula)
print("Clauses after turning conjunctions into clauses:", formula)
#

