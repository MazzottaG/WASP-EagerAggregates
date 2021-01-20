import sys
def getJoin(line):
    terms_split = line.split("a_X_Y_b_Y_(")[1].split(")")[0].split(",")
    terms = []
    for t in terms_split:
        terms.append(t)
    return terms

if "--check" in sys.argv:
    results=[]
    #a_X_Y_b_Y_(2,1,1)
    files=["std_out","debug/joinTuples"]
    sums_files=[]
    for file_ in files:
        f = open(file_,"r")
        lines = f.read().splitlines()
        negative={"undef":[],"true":[]}
        positive={"undef":[],"true":[]}
        print(file_)
        sums={"positive":{"actual":[],"possible":[]},"negative":{"actual":[],"possible":[]}}

        for i in range(0,len(lines)):
        
            if lines[i]=="True join tuple":
                i+=1
                joins=[]
                while lines[i]!="Undef join tuple":
                    joins.append(getJoin(lines[i]))
                    i+=1
                # print(lines[i])
                positive["true"].append(joins)
                i+=1
                joins=[]
                while lines[i]!="Negative True join tuple":
                    joins.append(getJoin(lines[i]))
                    i+=1
                # print(lines[i])
                positive["undef"].append(joins)
                
                i+=1
                joins=[]
                while lines[i]!="Negative Undef join tuple":
                    if len(negative["true"]) ==80:
                        print(lines[i])
                        print(i)
                    joins.append(getJoin(lines[i]))
                    i+=1
                # print(lines[i])
                negative["true"].append(joins)
                if len(negative["true"]) ==81:
                    print(joins)
                i+=1
                joins=[]
                while "ActualSum: " not in lines[i]:
                    if len(negative["undef"]) ==80:
                        print(lines[i])
                        print(i)
                    joins.append(getJoin(lines[i]))
                    i+=1
                # print(lines[i])
                # if i > 1119:
                #     print("-------------------"+file_+"-------------------")
                #     print(joins)
                #     break
                
                negative["undef"].append(joins)
                if len(negative["undef"]) ==81:
                    print(joins)
                actualSum=lines[i].split("ActualSum: ")[1]
                sums["positive"]["actual"].append(actualSum)
                i+=1
                trueAggrVars=[]
                while "PossibleSum: " not in lines[i]:
                    trueAggrVars.append(lines[i])
                    i+=1
                # print(lines[i])
                possibleSum=lines[i].split("PossibleSum: ")[1]
                sums["positive"]["possible"].append(possibleSum)
                i+=1
                undefAggrVars=[]
                while "NegativeActualSum: " not in lines[i]:
                    undefAggrVars.append(lines[i])
                    i+=1
                # print(lines[i])
                
                actualNegativeSum=lines[i].split("NegativeActualSum: ")[1]
                sums["negative"]["actual"].append(actualNegativeSum)
                i+=1
                trueNegativeAggrVars=[]
                while "NegativPossibleSum: " not in lines[i]:
                    trueNegativeAggrVars.append(lines[i])
                    i+=1
                # print(lines[i])
                
                possibleNegativeSum=lines[i].split("NegativPossibleSum: ")[1]
                sums["negative"]["possible"].append(possibleNegativeSum)
                i+=1
                undefNegativeAggrVars=[]
                while "True " not in lines[i] and "Undef " not in lines[i] and "{" not in lines[i]:
                    undefNegativeAggrVars.append(lines[i])
                    i+=1
                # print(lines[i])
                # print(positive)
                # print(negative)
                
        f.close()
        sums_files.append(sums)
        print(sums)
        results.append([positive,negative])
    print(sums_files[0]==sums_files[1])
    keys=["true","undef"]
    for j in [0,1]:
        if j == 0 :
            print("Checking positive join")
        else:
            print("Checking negative join")
        for key in keys:
            i=0
            for join_set in results[0][j][key]:
                for join in join_set:
                    if join not in results[1][j][key][i]:
                        print(join_set)
                        print(results[1][j][key][i])
                        print(i)
                        exit(0)
                # print("wasp result in computed result")

                for join in results[1][j][key][i]:
                    if join not in join_set:
                        print(join_set)
                        print(results[1][j][key][i])
                        print(i)
            # print("Computed result in wasp result")
                i+=1
    exit(0)
undef_a=[]
undef_b=[]
true_a=[]
true_b=[]
false_a=[]
false_b=[]
f = open("std_out","r")
i=0
for line in f.read().splitlines():
    if "Undef " in line and "(" in line:
        print(line)
        line=line.split("Undef ")[1]
        negated=False
        if line[0]=="-":
            negated=True
            line=line[1:]
        pred = line.split("(")[0]
        terms_split = line.split("(")[1].split(")")[0].split(",")
        terms=[]
        for t in terms_split:
            terms.append(int(t))
        if pred == "a":
            if negated:
                if terms in false_a:
                    false_a.remove(terms)
            else:
                if terms in true_a:
                    true_a.remove(terms)
            if terms not in undef_a:
                undef_a.append(terms)
        else:
            if pred == "b":
                if negated:
                    if terms in false_b:
                        false_b.remove(terms)
                else:
                    if terms in true_b:
                        true_b.remove(terms)
                if terms not in undef_b:
                    undef_b.append(terms)
        true_negative_join=[]
        undef_negative_join=[]
        true_join=[]
        undef_join=[]
        
        for a in true_a+undef_a+false_a:
            for b in true_b+undef_b+false_b:
                if a[1]==b[0]:
                    join = []
                    for v in a:
                        join.append(v)
                    for v in b:
                        join.append(v)
                    if join[0]<0:
                        if a in false_a or b in false_b:
                            if join not in true_negative_join:
                                true_negative_join.append(join)
                        else:
                            if a not in true_a or b not in true_b:
                                if join not in undef_negative_join:
                                    undef_negative_join.append(join)
                    else:
                        if a in true_a and b in true_b:
                            if join not in true_join:
                                true_join.append(join)
                        else:
                            if a not in false_a and b not in false_b:
                                if join not in undef_join:
                                    undef_join.append(join)
        print("True join tuple")
        actualSum=0
        truAggrVars=[]
        for j in true_join:
            actualSum+=j[0]
            if j[0] not in truAggrVars:
                truAggrVars.append(j[0])
            s = "a_X_Y_b_Y_("
            for t in j:
                s+=str(t)+","
            s=s[:-1]
            s+=")"
            print(s)
        print("Undef join tuple")
        possibleSum=0
        undefAggrVars=[]
        for j in undef_join:
            possibleSum+=j[0]
            if j[0] not in undefAggrVars:
                undefAggrVars.append(j[0])
            
            s = "a_X_Y_b_Y_("
            for t in j:
                s+=str(t)+","
            s=s[:-1]
            s+=")"
            print(s)
        print("Negative True join tuple")  
        actualNegativeSum=0
        trueNegativeAggrVars=[]
        for j in true_negative_join:
            actualNegativeSum+=j[0]*-1
            if j[0]*-1 not in trueNegativeAggrVars:
                trueNegativeAggrVars.append(j[0]*-1)
            s = "a_X_Y_b_Y_("
            for t in j:
                s+=str(t)+","
            s=s[:-1]
            s+=")"
            print(s)
        print("Negative Undef join tuple")    
        possibleNegativeSum=0
        undefNegativeAggrVars=[]
        for j in undef_negative_join:

            possibleNegativeSum+=j[0]*-1
            if j[0]*-1 not in undefNegativeAggrVars:
                undefNegativeAggrVars.append(j[0]*-1)
            s = "a_X_Y_b_Y_("
            for t in j:
                s+=str(t)+","
            s=s[:-1]
            s+=")"
            print(s)
        print("ActualSum: "+str(actualSum))
        for t in truAggrVars:
            print(t)
        print("PossibleSum: "+str(possibleSum))
        for t in undefAggrVars:
            print(t)
        print("NegativeActualSum: "+str(actualNegativeSum))
        for t in trueNegativeAggrVars:
            print(t)
        
        print("NegativPossibleSum: "+str(possibleNegativeSum))
        for t in undefNegativeAggrVars:
            print(t)
        
        print("{")
        i+=1
    else:
        if "True " in line and "(" in line:
            print(line)
            line=line.split("True ")[1]
            negated=False
            if line[0]=="-":
                negated=True
                line=line[1:]
            pred = line.split("(")[0]
            terms_split = line.split("(")[1].split(")")[0].split(",")
            terms=[]
            for t in terms_split:
                terms.append(int(t))
            if pred == "a":
                if negated:
                    if terms not in false_a:
                        false_a.append(terms)
                else:
                    if terms not in true_a:
                        true_a.append(terms)
                if terms in undef_a:
                    undef_a.remove(terms)
            else:
                if pred == "b":
                    if negated:
                        if terms not in false_b:
                            false_b.append(terms)
                    else:
                        if terms not in true_b:
                            true_b.append(terms)
                    if terms in undef_b:
                        undef_b.remove(terms)
            true_negative_join=[]
            undef_negative_join=[]
            true_join=[]
            undef_join=[]
            
            for a in true_a+undef_a+false_a:
                for b in true_b+undef_b+false_b:
                    if a[1]==b[0]:
                        join = []
                        for v in a:
                            join.append(v)
                        for v in b:
                            join.append(v)
                        if join[0]<0:
                            if a in false_a or b in false_b:
                                if join not in true_negative_join:
                                    true_negative_join.append(join)
                            else:
                                if a not in true_a or b not in true_b:
                                    if join not in undef_negative_join:
                                        undef_negative_join.append(join)
                        else:
                            if a in true_a and b in true_b:
                                if join not in true_join:
                                    true_join.append(join)
                            else:
                                if a not in false_a and b not in false_b:
                                    if join not in undef_join:
                                        undef_join.append(join)
            print("True join tuple")
            actualSum=0
            truAggrVars=[]
            for j in true_join:
                actualSum+=j[0]
                if j[0] not in truAggrVars:
                    truAggrVars.append(j[0])
                s = "a_X_Y_b_Y_("
                for t in j:
                    s+=str(t)+","
                s=s[:-1]
                s+=")"
                print(s)
            print("Undef join tuple")
            possibleSum=0
            undefAggrVars=[]
            for j in undef_join:
                possibleSum+=j[0]
                if j[0] not in undefAggrVars:
                    undefAggrVars.append(j[0])
                
                s = "a_X_Y_b_Y_("
                for t in j:
                    s+=str(t)+","
                s=s[:-1]
                s+=")"
                print(s)
            print("Negative True join tuple")  
            actualNegativeSum=0
            trueNegativeAggrVars=[]
            for j in true_negative_join:
                actualNegativeSum+=j[0]*-1
                if j[0]*-1 not in trueNegativeAggrVars:
                    trueNegativeAggrVars.append(j[0]*-1)
                s = "a_X_Y_b_Y_("
                for t in j:
                    s+=str(t)+","
                s=s[:-1]
                s+=")"
                print(s)
            print("Negative Undef join tuple")    
            possibleNegativeSum=0
            undefNegativeAggrVars=[]
            for j in undef_negative_join:

                possibleNegativeSum+=j[0]*-1
                if j[0]*-1 not in undefNegativeAggrVars:
                    undefNegativeAggrVars.append(j[0]*-1)
                s = "a_X_Y_b_Y_("
                for t in j:
                    s+=str(t)+","
                s=s[:-1]
                s+=")"
                print(s)
            print("ActualSum: "+str(actualSum))
            for t in truAggrVars:
                print(t)
            print("PossibleSum: "+str(possibleSum))
            for t in undefAggrVars:
                print(t)
            print("NegativeActualSum: "+str(actualNegativeSum))
            for t in trueNegativeAggrVars:
                print(t)
            
            print("NegativPossibleSum: "+str(possibleNegativeSum))
            for t in undefNegativeAggrVars:
                print(t)
            
            print("{")
            i+=1
print(i)
f.close()