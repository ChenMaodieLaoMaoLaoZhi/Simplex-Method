%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
function [x,fval,flag]=MyLPSolver(varargin)
    switch nargin
        case 3
            f=varargin{1};
            A=varargin{2};
            b=varargin{3};
            [x,fval,flag]=MyLPSolver1(f,A,b);
        case 5
            f=varargin{1};
            A=varargin{2};
            b=varargin{3};
            Aeq=varargin{4};
            beq=varargin{5};
            [x,fval,flag]=MyLPSolver2(f,A,b,Aeq,beq);
        case 7
            f=varargin{1};
            A=varargin{2};
            b=varargin{3};
            Aeq=varargin{4};
            beq=varargin{5};
            lb=varargin{6};
            ub=varargin{7};
            [x,fval,flag]=MyLPSolver3(f,A,b,Aeq,beq,lb,ub);
        otherwise 
            error('Parameter error');
    end
end
function [x,fval,flag]=MyLPSolver1(f,A,b)
    except=size(A,2);
    [new_f,new_A]=change3(f,A,size(A,2));
    [x,fval,flag]=StandardSolver(new_f,new_A,b,except);
end
function [x,fval,flag]=MyLPSolver2(f,A,b,Aeq,beq)
    [f,A,new_b,except]=change2(f,A,b,Aeq,beq);
    [new_f,new_A]=change3(f,A,except);
    [x,fval,flag]=StandardSolver(new_f,new_A,new_b,except);
end
function [x,fval,flag]=MyLPSolver3(f,A,b,Aeq,beq,lb,ub)
    %将等式约束并入不等约束中
    except=size(A,2);
    [f,A,b,lb,ub]=change01(f,A,b,Aeq,beq,lb,ub);
    %对变量做平移变换，并加入上界的约束条件,改变A,b
    A_len=size(A,2);
    offset=lb;
    record=zeros(1,A_len);
    record2=false(1,A_len);%case:上界为inf，表示要删除的行
    upper_constraint=zeros(1,A_len);
    constraints=zeros(A_len,A_len);
    traint_bs=zeros(A_len,1);
    for i=1:A_len
        if lb(i)==-inf
            offset(i)=0;
            record(i)=1;
        end
        if ub(i)==inf
            record2(i)=true;
            continue
        else
            upper_constraint(i)=1;
            constraints(i,:)=upper_constraint;
            traint_bs(i)=ub(i)-lb(i);
        end
    end
    constraints(record2,:)=[];
    traint_bs(record2)=[];
    %偏移量对b的影响，对f的影响用sum_offset表示
    b=b+A*offset;
    A=[A;constraints];
    b=[b;traint_bs];
    sum_offset=f*offset(1:A_len);
    %准备对无约束变量进行分解,改变f,A
    change1=find(record);
    l_len=size(change1,2);
    add_num=0;
    for j=1:l_len
        origin_index=change1(j);
        change1(j)=origin_index+add_num;
        add_num=add_num+1;
    end
    for index=change1
        ahead_f=[f(1:index),-f(index)];
        behind_f=f(index+1:A_len);
        f=[ahead_f,behind_f];
        column=A(:,index);
        ahead_A=[A(:,1:index),-column];
        behind_A=A(:,index+1:A_len);
        A=[ahead_A,behind_A];
    end
    %已全部化为标准问题
    [x,fval,flag]=StandardSolver(f,A,b,except);
    fval=fval-sum_offset;
end
function [x,fval,flag]=StandardSolver(f,A,b,except_bound)
    n=size(A,1);
    m=size(f,2);
    %矩阵扩增
    %寻找初始可行解的辅助问题
    I=eye(n);
    y=ones(1,n);%行向量
    origin_f=[zeros(1,m),y];
    origin_A=[A,I];
    endlen=size(origin_f,2);
    x=zeros(endlen,1);%包含全部变量名的列向量
    assit_location=find(origin_f);%展示
    assit_can=[origin_f,0;origin_A,b];
    ignores=endlen-(n-except_bound)+1:endlen;
    [new_can,new_location]=Simplex(assit_can,assit_location);
    cohave=intersect(assit_location,new_location);
    cohave_len=size(cohave,2);
    %判断是否有解
    if size(intersect(assit_location,new_location),2)==0 || size(intersect(cohave,ignores),2)==cohave_len
        new_r=[f,zeros(1,endlen+1-m)];%注意
        new_can(1,:)=[];
        new_can=[new_r;new_can];%展示
        [result_canonical,result_location]=Simplex(new_can,new_location);
        if size(result_location,2)==0
            x=NaN;
            fval=NaN;
            flag='unbounded'
            return
        elseif all(result_location==1)
            x=NaN;
            fval=NaN;
            flag='infeasible'
            return
        end
        rs_width=size(result_canonical,1);
        rs_len=size(result_canonical,2);
        valued_x=result_canonical(2:rs_width,rs_len);
        j=0;
        for i = result_location
            j=j+1;
            x(i)=valued_x(j);
        end
        fval=f(1:2*except_bound)*x(1:2*except_bound);
        flag='simple result'
    else
        x=NaN;
        fval=NaN;
        flag='ineasible'
        return
    end
end
function [canonical,location]=Simplex(canonical,location)
    width=size(canonical,1);
    lenth=size(canonical,2);
    combination=location;
    while true
        A=canonical(2:width,1:lenth-1);
        b=canonical(2:width,lenth);
        r=canonical(1,:);
        Cb=canonical(1,location);%行向量
        Ab=canonical(2:width,location);
        %在当前location下化为规范型
        A=lsqminnorm(Ab,A);
        b=lsqminnorm(Ab,b);
        A_all=[A,b];
        r=r-Cb*A_all;
        canonical=[r;A,b]
        canonical(abs(canonical)<0.000001)=0;
        c=canonical(1,1:lenth-1);
        if all(c>=0)
            break
        end
        pre_in=find(c<0);
        old_location=location;
        for in=pre_in
            pre_out=A(:,in);
            if all(pre_out<=0)
                location=[];
                return
            else
                lines=find(pre_out>0);
                min=inf;
                for i=lines.'
                    if min>(b(i)/pre_out(i))
                        min=b(i)/pre_out(i);
                        minline=i;
                    end
                end
                out=minline;
                old_location=location;
                location(out)=in;
                if all(ismember(location,combination)==1)
                    %不选选过的解基
                    location=old_location;
                    continue
                else
                    combination=[combination;location];  %#ok<AGROW>
                    break
                end
            end
        end
        if location==old_location
            lo_len=size(location,2);
            location=ones(1,lo_len);
            return
        end
    end
end
function [f,A,b,lb,ub]=change01(f,A,b,Aeq,beq,lb,ub)
    %并入的新变量都有下界0
    [f,A,b]=change2(f,A,b,Aeq,beq);
    lb_len=size(lb,1);
    A_len=size(A,2);
    lb=[lb;zeros(A_len-lb_len,1)];
    ub=[ub;inf(A_len-lb_len,1)];
end
function [new_f,new_A,new_b,except]=change2(f,A,b,Aeq,beq)
    %处理等式约束 like in 2
    f_len=size(f,2);
    A_width=size(A,1);
    Aeq_width=size(Aeq,1);
    except=size(A,2);
    I=eye(A_width);
    all_A=[A,I];
    allA_len=size(all_A,2);
    new_Aeq=[Aeq,zeros(Aeq_width,A_width)];
    new_f=[f,zeros(1,allA_len - f_len)];
    new_A=[all_A;new_Aeq];
    new_b=[b;beq];
end
function [new_f,new_A]=change3(f,A,except)
    %无约束变量化为有约束
    A_len=size(A,2);
    Ac=A(:,1:except);
    new_f=zeros(1,2*except);
    A_width=size(Ac,1);
    new_A=zeros(A_width,except*2);
    for i=1:except
        %无约束问题目标函数转化为标准问题目标函数
        new_f(2*i-1)=f(i);
        new_f(2*i)=-f(i);
        column=A(:,i);
        new_A(:,2*i-1)=column;
        new_A(:,2*i)=-column;
    end
    new_A=[new_A,A(:,except+1:A_len)];
    new_f=[new_f,f(except+1:A_len)];
end