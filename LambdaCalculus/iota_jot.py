from LambdaCalculus.utlc import *
import time

# -- Constants --
x = Variable('x')
y = Variable('y')
z = Variable('z')

I = (x - x)
S = (x - (y - (z - ((x(z))(y(z))))))
K = (x - (y - x))

iota = (x - (x(S)(K)))


# Iot Interpreter
def _iot(prog):
    if len(prog) == 0:
        raise SyntaxError('Invalid Iota syntax.')
    elif prog[0] == 'i':
        return iota, prog[1:]
    elif prog[0] == '`' or prog[0] == '*':
        A, s = _iot(prog[1:])
        B, s = _iot(s)
        return A(B), s
    else:
        raise SyntaxError('Unexpected character.')


def IotInterpret(prog):
    p, s = _iot(prog)
    if len(s) != 0:
        raise SyntaxError('Invalid Iota syntax.')
    return p


# print(IotInterpret('`i`i`ii').reduction())

# Jot Interpreter
def JotInterpret(prog):
    pr = I
    for i in prog:
        if i == '1':
            pr = pr(S)(K)
        elif i == '0':
            pr = (x - (y - (pr(x(y)))))
        else:
            raise SyntaxError('Unexpected character')
    return pr


# print(JotInterpret('11111000').reduction())
# print(JotInterpret('101110101010011010101001000'))
if __name__ == '__main__':
    print('!!!!!!!!!!!!!!!!!!!!!!!!!!')
    print('! Pyjot Interpreter REPL !')
    print('!!!!!!!!!!!!!!!!!!!!!!!!!!')
    while True:
        try:
            inp = input('In > ')
            if len(inp) == 0:
                continue
            elif inp == 'exit':
                print('All Hail Lambda Calculus!!')
                break
            elif inp == 'jot':
                n = 0
                while True:
                    print(n, JotInterpret(bin(n)[2:]).reduction())
                    n += 1
                    time.sleep(1)
            elif inp[0] in ['i', '*', '`']:
                print('Iot>', IotInterpret(inp).reduction())
            elif inp[0] in ['1', '0']:
                print('Jot>', JotInterpret(inp).reduction())
            elif inp[0] == 'j' and len(inp) > 1:
                print('Jot>', JotInterpret(bin(int(inp[1:]))[2:]).reduction())
            else:
                print('Err: Not a valid expression.')
        except SyntaxError as e:
            print('Err: Syntax Error.')
        except RuntimeError as e:
            print('Err: Possibly non-terminating.')
        except KeyboardInterrupt as k:
            print('Err: User Interrupted.')
        except ValueError as v:
            print('Err: Not a valid expression.')
