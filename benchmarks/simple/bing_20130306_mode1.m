function dy = mode1(t,y)
dy = zeros(4,1);
thetaw=0.13;
thetav=0.3;
us=0.9087;
uu=1.55;
winfstar=0.94;
ks=2.0994;
gvp=0.68936;
gwp=0.005;
gv1n=0.01666;
gv2n=0.00086;
gwn=0.01666;
gw1n=0.01666;
gw2n=0.06666;
go1=0.0025;
go2=0.16666;
gso=0.33331;
gso1=0.03331;
gso2=1.00431;
gs1=0.36453;
gs2=0.0625;
gfi=9.0909;
gsi=0.5298;
e=2.7182;
gwinf=142.8571;

dy(1) = e + (y(1) - thetav) * (uu - y(1)) * y(2) * gfi + y(3) * y(4) * gsi  - gso * y(1);
dy(2) = - y(2) * gvp;
dy(3) = - y(3) * gwp;
dy(4) = 1 / (1.001+ exp(-2 * ks * (y(1) - us))) - y(4) * gs2;

%options = odeset('RelTol',1e-4,'AbsTol',[1e-4 1e-4 1e-4 1e-4]);
%[T,Y] = ode15s(@mode1,[0 12],[0.3 1 1 0.001],options);
% plot(T,Y(:,1),'-',T,Y(:,2),'-.',T,Y(:,3),'.',T,Y(:,4),'x')
