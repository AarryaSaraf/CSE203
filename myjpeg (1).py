# -*- coding: utf-8 -*-
"""
Created on Wed May 25 16:38:04 2022

@author: Aarrya
"""


import math
#alist makes it so that alpha values between 1 and 8 do not need 
#to be repeatedly calculated as it wastest time
# instead we just store it as cache


# Throughout this project all the algorithms 
# implemented have followed the logic which was 
# metioned or a comment highlights my thought process 
# behind it


alist=[]
for i in range(0,9):
    alist.append(math.cos((i/16)*math.pi))
    
def ppm_tokenize(stream):
    """ DESCRIPTION
    -----------------
    use, inputs, and outputs as described."""
    # a common strategy for the following functions is 
    # to take the entire file as a string or vice versa
    # this makes it so that we do not need to know 
    # functions for files and can instead just use our seen
    # information and doing basic write and read only.
    a=stream.readlines()
    arr=[]
    for s in a:
        i=s.find('#')
        u=s
        if i>=0:
            u=s[:i]
        brr=[]
        while True:
            if len(u)==0:
                break
            i=u.find(' ')
            brr.append(u[:i])
            u=u[i+1:]
        for z in brr:
            if(z):
                arr.append(z)
    return arr
            
        
def ppm_load(stream):
    """ DESCRIPTION
    ---------------
    use, inputs, and outputs as described.
    Complexity O(w*h) where w and h are the width and height 
    as given in the input"""
    w=0
    h=0
    a=ppm_tokenize(stream)
    w=int(a[1])
    h=int(a[2])
    arr=[]
    c=4
    for i in range(0,h):
        brr=[]
        for j in range(0,w):
            crr=[]
            for k in range(0,3):
                crr.append(a[c])
                c=c+1
            brr.append((a[c-3],a[c-2],a[c-1])) 
        arr.append(brr)               
    return w,h,arr



def ppm_save(w,h,img,output):
    """ DESCRIPTION
    ---------------
    use, inputs, and outputs as described.
    Complexity O(w*h)"""
    with open(output,'w') as out:
        s="P3 \n"+str(w)+" "+str(h)+"\n"+"255"+"\n"
        for i in range(0,h):
            for j in range(0,w):
                a,b,c=img[i][j]
                s=s+str(a)+"\t"+str(b)+"\t"+str(c)+"\n"
        out.write(s)
    

def RGB2YCbCr(r, g, b):
    """ DESCRIPTION
    ---------------
    use, inputs, and outputs as described. Complexity=O(1)"""
    y=min(max(round(0.299*r +0.587*g +0.114*b),0),255)
    cb=min(max(round(128 -0.168736*r -0.331264*g +0.5*b),0),255)
    cr=min(max(round(128 +0.5*r -0.418688*g -0.081312*b),0),255)    
    return(y,cb,cr)

def YCbCr2RGB(y,cb,cr):
    """ DESCRIPTION
    ---------------
    use, inputs, and outputs as described. Complexity=O(1) """
    r=min(max(round(y +1.402*(cr-128)),0),255)
    g=min(max(round(y -0.344136*(cb-128) -0.714136*(cr-128)),0),255)
    b=min(max(round(y +1.772*(cb-128)),0),255)
    return(r,g,b)
    
def img_RGB2YCbCr(img):
    """ DESCRIPTION
    -------------------
    use, inputs, and outputs as described. Complexity O(n*m)
    where n and m denote the width of height of the input matrix
    ."""
    # A common style that I have used throughout this project is to
    # make multiple 1D arrays and append them to an array in 
    # order to make 1 2D array. While this might not be 
    #practical for larger dimensions our project 
    # did not deal with more than 2 and hence it was fine
    h=len(img)
    w=len(img[0])
    y=[]
    cb=[]
    cr=[]
    for i in range(0,h):
        yr=[0]*w
        cbr=[0]*w
        crr=[0]*w
        for j in range(0,w):
            yr[j],cbr[j],crr[j]=RGB2YCbCr(img[i][j])
        y.append(yr)
        cb.append(cbr)
        cr.append(crr)
    return((y,cb,cr))

def img_YCbCr2RGB(y, cb, cr):  
    """ DESCRIPTION
    ----------------
    use, inputs, and outputs as described. Complexity O(n*m)
    where n and m denote the width of height of the input matrix """
    img=[]
    h=len(y)
    w=len(y[0])
    for i in range(0,h):
        arr=[0]*w
        for j in range(0,w):
            arr.append(YCbCr2RGB(y[i][j],cb[i][j,cr[i][j]]))
        img.append(arr)
    return img
    
def subsampling(w, h, img, h2, w2):
    """ DESCRIPTION
    ----------------
    use, inputs, and outputs as described. Complexity O(a*b)
    """
    # Explanation: we notice that we can divide our width into 
    # w/w2 number of blocks and for the final parts (if any) left 
    # out then we can combine the min and ceil functions to do 
    # that job. The next 2 functions follow a similar logic.
    # Another common theme
    # Instead of using a and b as inputs as mentioned
    # I have used r and c. This obviously does not change anything 
    # but r and c stand for row and column and help
    # with readability
    brr=[]
    for i in range(0,math.ceil(h/h2)):
        arr=[]
        for j in range(0,math.ceil(w/w2)):
            s=0
            for ii in range(h2*i,min(h2*(i+1),h)):
                for jj in range(w2*j,min(w2*(j+1),w)):
                    s=s+img[ii][jj]
            q=(min(h2*(i+1),h)-(h2*i))*((min(w2*(j+1),w)-(w2*j)))
            arr.append(round(s/q))
        brr.append(arr)
    return brr

def extrapolate(w, h, img, h2, w2):
    """ DESCRIPTION
    ----------------
    use, inputs, and outputs as described. Complexity O(w*h)
    """   
    arr=[[0 for j in range(w)] for i in range(h)]
    for i in range(0,math.ceil(h/h2)):
        for j in range(0,math.ceil(w/w2)):
            print(str(i)+" "+str(j))
            for k in range(i*h2,min(h,(i+1)*h2)):
                for l in range(j*w2,min(w,(j+1)*w2)):
                    arr[k][l]=img[i][j]
    return arr

def block_splitting(w, h, img):
    """ DESCRIPTION
    ---------------
    use, inputs, and outputs as described. Complexity O(w*h)"""
    for i in range(0,(math.ceil(h/8))):
        for j in range(0,(math.ceil(w/8))):
            brr=[]
            for ii in range(8*i,8*(i+1)):
                arr=[]
                for jj in range(8*j,8*(j+1)):
                    arr.append(img[min(ii,h-1)][min(jj,w-1)])
                brr.append(arr)
            yield brr
                
def mat(s):
    """ DESCRIPTION
    --------------
    use- to create the desired matrix
    inputs- side length of matrix
    outputs- the matrix
    Complexity- O(s^2) """
    m=[]
    for i in range(0,s):
        arr=[]
        for j in range(0,s):
            de=1
            if(i==0):
                de=1/math.sqrt(2)
            c=math.cos((math.pi/s)*(j+1/2)*i)
            ele=de*math.sqrt(2/s)*c
            arr.append(ele)
        m.append(arr)
    return m
           
def trans(m):  
    """ DESCRIPTION
    ---------------
    use- transposes a matrix
    input- a matrix
    output- the matrix but transposed
    complexity- O(w*h) where w and h are the width and height
    of the input matrix"""
    # we start by noticing that transpose would just mean 
    #swapping i and j
    arr = [[0 for j in range(len(m))] for i in range(len(m[0]))]
    for i in range(0,len(m[0])):
        for j in range(0,len(m)):
            arr[i][j]=m[j][i]
    return arr
   
def mult(v,m):
    """ DESCRIPTION
    -----------------
    use- to multiply a vector by a square matrix
    input- the vector and square matrix
    output- the product vector
    complexity- O(s^2) where s is the length of the input 
    matrix"""
    brr=[]
    for i in range(0,len(m)):
        c=0
        for j in range(0,len(m)):
            c=c+v[j]*m[j][i]
        brr.append(c)
    return brr
    
def mult2D(a,m):
    """ DESCRIPTION
    -------------
    use- to multiply a 2d matrix with a square 2d matrix
    input- the two matrices
    output- the product matrix
    complexity- O(n*s^2) where s is the length of the square
    matrix and n is the number of rows of the input matrix"""
    # we start by noticing that mutiplying multiple rows
    # is the same as doing each row and appending that
    arr=[]
    for i in a:
        arr.append(mult(i,m))
    return arr

def DCT(v):
    """ DESCRIPTION
    ----------------
    use, inputs, and outputs as described. Complexity O(s^2)
    where s is the length of the input vector"""
    return (mult(v,trans(mat(len(v)))))

def IDCT(v):
    """ DESCRIPTION
    --------------
    use, inputs, and outputs as described. Complexity O(s^2)
    where s is the length of the input vector"""
    return (mult(v,(mat(len(v)))))
    
def DCT2(r,c,a):
    """ DESCRIPTION
    --------------
    use, inputs, and outputs as described. 
    Complexity O(r*c^2)"""
    #Another common theme in my project. 
    # Instead of looping over the columns and doing the same 
    # procedure we can just transpose the matrix which 
    # saves us time in writing the code as we already have a 
    # function for it and it does not change the complexity
    # of our function
    arr=(mult2D(a,trans(mat(c))))
    arr=trans(arr)
    ar=(mult2D(arr,trans(mat(r))))
    return(trans(ar))
    
def IDCT2(r,c,a):
    """ DESCRIPTION
    ---------------
    use, inputs, and outputs as described. 
    Complexity O(r*c^2) """
    arr=(mult2D(a,mat(c)))
    arr=trans(arr)
    ar=(mult2D(arr,(mat(r))))
    return(trans(ar))

def redalpha(i):
    """ DESCRIPTION
    -------------
    use, inputs, and outputs as described. Complexity O(1) """
    # we start by noticing cosine properties
    # cos(x+2pi)=cos(x)
    # cos(-x)=cos(x)
    # etc etc
    k=i//32
    i=i-(k*32)
    if(i>24):
        return(1,32-i)
    elif(i>16):
        return(-1,i-16)
    elif(i>8):
        return(-1,16-i)
    elif(i>0):
        return(1,i)
    else:
        return(-1,1)
    
def ncoeff8(i,j):
    """ DESCRIPTION
    ---------------
    use, inputs, and outputs as described. Complexity O(1) """
    if(i==0):
        return(1,4)
    else:
        return(redalpha(i+(j*i*2)))
      
def alpha(i):
    """ DESCRIPTION
    -------------------
    use- gives the alpha value of i
    input- i, the number whos alpha we calculate
    output- the desired value
    Complexity O(1) """
    # Again as stated before we can see that by just barely
    # using any memory we can save a lot of time in 
    # unecessary calculations
    x,y=redalpha(i)
    return(x*alist[y])

def mult2(v):
    """ DESCRIPTION
    -----------------
    use- this is the main logic behind DCT chen
    inputs- a vector v
    outputs a vector made using chens algorithms
    Complexity O(1) """
    #multiplications per row denoted by mul
    a=[]
    for i in range(0,8):
        s=0        
        if(i==0):
            for i in range(0,8):
                s=s+v[i]
            s=s*alpha(4)
        #mul = 1
        elif(i==2):
            q=v[0]+v[7]-v[3]-v[4]
            b=v[1]+v[6]-v[2]-v[5]
            s=alpha(2)*q+alpha(6)*b
        #mul = 3
        elif(i==4):
            q=v[0]+v[7]+v[3]+v[4]-v[1]-v[6]-v[2]-v[5]
            s=alpha(4)*q
        #mul = 4
        elif(i==6):
            q=v[0]+v[7]-v[3]-v[4]
            b=v[2]+v[5]-v[1]-v[6]
            s=alpha(6)*q+alpha(2)*b
        #mul = 6
        else:
            w=-1
            if(i%2==0):
                w=1
            for j in range(0,4):
                x,y=ncoeff8(i,j)
                s=s+((v[j]+w*v[7-j])*x*alpha(y))       
        a.append(s/2)
        #mul = 6 + (4*4)=6+16=22
    # 22 multiplications per row which means 176 for rows
    # this would mean a total of 352 multiplications for rows
    # and columns which is our desired number
    return a

def DCT_chen(a):
    """ DESCRIPTION
    -----------------
    use, inputs, and outputs as described. Complexity O(w*h) 
    due to the transpose function"""
    ar=[]
    arr=[]
    for i in a:
        ar.append(mult2(i))
    ar=trans(ar)
    for i in ar:
        arr.append(mult2(i))
    return trans(arr)


def IDCT_chen_mult(v):
    """ DESCRIPTION
    ------------------
    use- multiplying our vector with the omega and theta 
    matrices. This function does the main work
    for IDCT chen
    input- a vector v
    output- the vector but after the IDCT transform using 
    Chen's algorithms
    Complexity O(1) """
    o=IDCT_chen_o()
    t=IDCT_chen_t()
    arr=[0]*8
    for i in range(0,4):
        x=0
        y=0
        for j in range(0,4):
            x+=v[j]*o[j][i]
            y+=v[4+j]*t[j][i]
        arr[i]=x+y
        arr[i+4]=x-y
    return arr

def IDCT_chen_o():
    """DESCRIPTION
    ----------------
    use, inputs, and outputs as described. Complexity O(n) """
    o=[]
    o.append([alpha(4)]*4)
    o.append([alpha(2),alpha(6),-alpha(6),-alpha(2)])
    o.append([alpha(4),-alpha(4),-alpha(4),alpha(4)])
    o.append([alpha(6),-alpha(2),alpha(2),-alpha(6)])
    return o
    
def IDCT_chen_t():
    """ DESCRIPTION
    -----------------
    use- used to create the theta matrix
    no inputs
    output- theta matrix
    I did not want to put this outside of the functions purely
    for the freedom of choosing variable names
    Complexity-O(1)"""
    t=[]
    t.append([])
    for i in range(1,8,2):
        t[0].append(alpha(i))
    t.append([alpha(3),-alpha(7),-alpha(1),-alpha(5)])
    t.append([alpha(5),-alpha(1),alpha(7),alpha(3)])
    t.append([alpha(7),-alpha(5),alpha(3),-alpha(1)])
    return t
    
def IDCT_chen_help(a):
    """ DESCRIPTION
    ---------------
    use- used to create the omega matrix
    no inputs
    output- theta matrix
    I did not want to put this outside of the functions purely
    for the freedom of choosing variable names
    Complexity-O(1)"""
    m=[]
    for i in range(0,8):
        ar=a[i]
        arr=[]
        for k in range(0,8,2):
            arr.append(ar[k]/2)
        for k in range(1,8,2):
            arr.append(ar[k]/2)
        br=IDCT_chen_mult(arr)
        brr=[]
        for k in range(0,4):
            brr.append(br[k])
        for k in range(7,3,-1):
            brr.append(br[k])
        m.append(brr)  
    return m

def IDCT_chen(a):
    """ DESCRIPTION
    -----------------
    use, inputs, and outputs as described. Complexity O(1) """
    arr=IDCT_chen_help(a)
    arr=trans(arr)
    return(trans(IDCT_chen_help(arr)))

def quantization(A,Q):
    """ DESCRIPTION
    ----------------
    use, inputs, and outputs as described. Complexity O(1) """
    m=[]
    for i in range(0,8):
        arr=[]
        for j in range(0,8):
            arr.append(round(A[i][j]/Q[i][j]))
        m.append(arr)
    return m

def quantizationI(A,Q):
    """ DESCRIPTION
    ----------------
    use, inputs, and outputs as described. Complexity O(1) """
    m=[]
    for i in range(0,8):
        arr=[]
        for j in range(0,8):
            arr.append(A[i][j]*Q[i][j])
        m.append(arr)
    return m

def zigzag(A):
    """ DESCRIPTION
    --------------
    use, inputs, and outputs as described. Complexity O(1)
    """
    # we start by noticing that there are only 4 possible 
    # directions and the direction remains constant 
    # unless specific conditions are met which are 
    # the if statements
    i=0
    j=0
    d=0
    arr=[]
    for k in range(0,64):
        #print(str(i)+" "+str(j))
        arr.append(A[i][j])
        if(i==0):
            d=j%2
        elif(i==7):
            d=2*(j%2)
        elif(j==0):
            d=2+i%2 
        elif(j==7):
            d=1+(2*(i%2))
        if(d==0):
            j=j+1
        elif(d==3):
            i=i+1
        elif(d==2):
            i=i-1
            j=j+1
        elif(d==1):
            i=i+1
            j=j-1
    return arr
        
def rle0(g):
    """ DESCRIPTION
    --------------
    use, inputs, and outputs as described. Complexity O(n)
    where n denote the number of elements in g"""
    c=0
    arr=[]
    for i in g:
        if(i==0):
            c=c+1
        else:
            arr.append((c,i))
            c=0
    return arr












    