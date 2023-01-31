from assembly import assembly

auxreg = ["$zero", "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9", "$t10", "$t11", "$t12", "$t13", 
"$t14", "$t15", "$t16", "$a0", "$a1", "$a2", "$a3", "$a4", "$a5", "$a6", "$a7", "$a8", "$ad", "$v0", "$sp", "$md", "$ra"]

auxInst = ["ADD","ADDI","SUB","SUBI","MUL","DIV","AND","XOR","OR","NOT","SLT","SLET","SGT","SGET","SET","SR","SL","JR","J",
"JAL","BEQ","BNEQ","LOAD","STORE","IN","OUT","NOP","HLT"]

# $zero: possui sempre o valor 0
# $t: registradores temporarios
# $a: registradores de argumentos
# $ad: registrador de endereco para variaveis vetores como argumentos
# $v0: regsitrador de retorno de funcao int
# $sp: registrador de topo de pilha
# $md: resto de divisao
# $ra: endereco de retorno de chamada de funcao

class aux:
    def __init__(self, name, bin):
        self.Name = name
        self.Bin = bin

def binbits(x):
    bits = bin(x).split('b')[1]

    if len(bits) < 5:
        return '0' * (5 - len(bits)) + bits
    elif len(bits) == 5:
        return bits

def binbits17(x):
    bits = bin(x).split('b')[1]

    if len(bits) < 17:
        return '0' * (17 - len(bits)) + bits
    elif len(bits) == 17:
        return bits

def binbits27(x):
    bits = bin(x).split('b')[1]

    if len(bits) < 27:
        return '0' * (27 - len(bits)) + bits
    elif len(bits) == 27:
        return bits

regList = []
instruList = []

for i in range(0,len(auxreg)):
    a = aux(auxreg[i],binbits(i))
    regList.append(a)

for i in range(0,len(auxInst)):
    a = aux(auxInst[i],binbits(i))
    instruList.append(a)


def binary(filename,filenameTable):

    # Ordem assembly, labelMap, table 
    assemblyInstr = assembly(fileName,fileNameTable) 
    global regList
    global instruList
    binList = []
    a = ""

    for inst in assemblyInstr[0]:
        if (inst.LineKind == 0):
            
            # Formato 1
            if(inst.InstrucKind == "ADD" or inst.InstrucKind == "SUB" or inst.InstrucKind == "MUL" or inst.InstrucKind == "DIV"
                or inst.InstrucKind == "AND" or inst.InstrucKind == "OR" or inst.InstrucKind == "XOR" or inst.InstrucKind == "SLT"
                or inst.InstrucKind == "SLET" or inst.InstrucKind == "SGT" or inst.InstrucKind == "SGET" or inst.InstrucKind == "SET"):
                for var in instruList:
                    if inst.InstrucKind == var.Name:
                        a = var.Bin
                for var in regList:
                    if inst.Rd == var.Name:
                        a = a + var.Bin
                for var in regList:
                    if inst.R1 == var.Name:
                        a = a + var.Bin
                for var in regList:
                    if inst.R2 == var.Name:
                        a = a + var.Bin + '000000000000'
                        binList.append(a)
                
                a = ""

            # Formato 2
            elif(inst.InstrucKind == "ADDI" or inst.InstrucKind == "SUBI" or inst.InstrucKind == "LOAD" or inst.InstrucKind == "STORE" or 
            inst.InstrucKind == "BEQ" or inst.InstrucKind == "BNEQ"):
                for var in instruList:
                    if inst.InstrucKind == var.Name:
                        a = var.Bin
                for var in regList:
                    if inst.Rd == var.Name:
                        a = a + var.Bin
                for var in regList:
                    if inst.R1 == var.Name:
                        a = a + var.Bin
                
                if(inst.InstrucKind == "BEQ" or inst.InstrucKind == "BNEQ"):
                    inst.Label
                    for b in assemblyInstr[1]:
                        if (inst.Label == b.split()[0]):
                            Im =  int(b.split()[1])
                            Im = binbits17(Im)
                            a = a + Im
                            binList.append(a)
                            a = ""
                else:
                    Im =  int(inst.Im)
                    Im = binbits17(Im)
                    a = a + Im
                    binList.append(a)
                    a = ""
                
            
            # Formato 3
            elif(inst.InstrucKind == "NOT" or inst.InstrucKind == "SR" or inst.InstrucKind == "SL"):
                for var in instruList:
                    if inst.InstrucKind == var.Name:
                        a = var.Bin
                for var in regList:
                    if inst.Rd == var.Name:
                        a = a + var.Bin
                for var in regList:
                    if inst.R1 == var.Name:
                        a = a + var.Bin + "00000000000000000"
                        binList.append(a)
                
                a = ""

            # Formato 4
            elif(inst.InstrucKind == "JR" or inst.InstrucKind == "IN" or inst.InstrucKind == "OUT"):
                for var in instruList:
                    if inst.InstrucKind == var.Name:
                        a = var.Bin
                for var in regList:
                    if inst.Rd == var.Name:
                        a = a + var.Bin + "0000000000000000000000"
                        binList.append(a)

                a = ""

            
            # Formato 5
            elif(inst.InstrucKind == "J" or inst.InstrucKind == "JAL"):
                for var in instruList:
                    if inst.InstrucKind == var.Name:
                        a = var.Bin
                        
                
                flag = 0 
                for tab in assemblyInstr[2]:
                    if (tab.Name == inst.Label and tab.Scope == "global" ): 
                        b = tab.InstLine
                        a = a + binbits27(b)
                        binList.append(a)
                        flag = 1
                
                if(flag == 0):
                    for b in assemblyInstr[1]:
                        if (inst.Label == b.split()[0]):
                            Im =  int(b.split()[1])
                            Im = binbits27(Im)
                            a = a + Im
                            binList.append(a)
                            a = ""

                a = ""

            # Formato 6
            elif(inst.InstrucKind == "NOP" or inst.InstrucKind == "HLT"):
                for var in instruList:
                    if inst.InstrucKind == var.Name:
                        a = var.Bin + "000000000000000000000000000"
                        binList.append(a)

                a = ""
    
    arquivo = open("binary.txt", "a")
    for var in binList:
        arquivo.write(f"{var}\n")
    
    
    return binList


if __name__ == '__main__':
    fileName = "outParser.output"
    fileNameTable = "outAnalyze.output" 
    binInstr = binary(fileName,fileNameTable)
    print()
    print("Binario gerado!")

    

