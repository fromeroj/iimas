int i,j,k,iv,ix,bo,n,vel,direccion;
boolean movimiento_aleatorio,asignado;
Tablero t;

void setup() {  
  n=25;
  vel=3;
  size(500,500);
  t = new Tablero(n);
  movimiento_aleatorio=true;
}

void draw() {
  background(255);
  /*Las lineas del tablero*/
  for(i=0;i<=n;i++){
    line(50,50+400*i/n,450,50+400*i/n);
    line(50+400*i/n,50,50+400*i/n,450);   
  }
  t.move_all();
}

class Tablero{
  Robot[] robots;
  color c(int i){
    return color(65*i*7 % 255,65*i*5%255,65*11*7%255); 
  }
  
  void move_all(){
    for(k=0;k<n;k++){
      if(movimiento_aleatorio){
      opcion_aleatoria(robots[k]).display();
      }else{
      buena_opcion(robots[k]).display();
      }
    }
  }

 Robot opcion_aleatoria(Robot r){
   if(r.y0!=(n-1)){
     direccion=int(random(3));
     if(direccion==0  && esta_vacio(r,r.x0-1 , r.y0)){
       r.izquierda();
     }else if(direccion==1  && esta_vacio(r, r.x0+1,r.y0)){
       r.derecha();
     }else if( direccion==2 && esta_vacio(r,r.x0,r.y0+1)){
       r.arriba();
     }
   }
   return r;
 }

 Robot buena_opcion(Robot r){
   if(r.y0!=(n-1)){
     bo=cuadro_vacio(r.x0);
     if(r.x0 != bo){
       if(r.x0 > bo  && esta_vacio(r,r.x0-1 , r.y0)){
         r.izquierda();
       }else if(r.x0 < bo  && esta_vacio(r, r.x0+1,r.y0)){
         r.derecha();
       }
     }else if( r.y0<n-1 && esta_vacio(r,r.x0,r.y0+1)){
         r.arriba();
     }
   }
   return r;
 }

 int cuadro_vacio(int col){
   /* Si esta vacio en la columna damos esa*/
   if (esta_vacio(null,col,n-1)) return col;
   /* En otro caso damos la primer columna vacia*/
   for(ix=0;ix<n;ix++){
     if (esta_vacio(null,ix,n-1)) return ix;
   }
   return -1;
 }
 
  boolean esta_vacio(Robot r, int x,int y){
    //return true;
    if (0>x || x>=n || 0>y || y>=n) return false; 
    for(iv=0;iv<n;iv++){
      if(robots[iv]!=null && robots[iv]!=r){
        if((robots[iv].x0==x && robots[iv].y0==y) || 
           (robots[iv].x1==x && robots[iv].y1==y)){
          return false;
        }
      } 
    }
    return true;
  }

  int[] vacio_aleatorio(){
    boolean vacio=false;
    int[] coo=new int[2];
    while(!vacio){
      coo[0]=int(random(n));  
      coo[1]=int(random(n));
      vacio=esta_vacio(null,coo[0],coo[1]);
    }
    return coo;
  }
  
  Tablero(int n){
    robots=new Robot[n];
    for(j=0;j<n;j++){
      int[] coo=vacio_aleatorio();
      robots[j] = new Robot(c(j),coo[0],coo[1]); 
    }
  }
}

class Robot { 
  color c;
  int x0,y0,x1,y1;
  float xpos;
  float ypos;

  int xp(int x){return 50+400*x/n;}
  int yp(int y){return 450-400/n-400*y/n;}
  
  Robot(color cc, int x, int y) { 
    c = cc;
    x0=x;
    y0=y;
    x1=x;
    y1=y;
    xpos = xp(x);
    ypos = yp(y);
  }
  
  void display() {
    stroke(0);
    fill(c);
    rectMode(CENTER);
    rect(xpos+200/n ,ypos+200/n,200/n,200/n);
  }  
  
  void arriba(){
    move(this.x0,this.y0+1);
  }
  void abajo(){
    move(this.x0,this.y0-1);
  }
  void izquierda(){
    move(this.x0-1,this.y0);
  }
  void derecha(){
    move(this.x0+1,this.y0);
  }
  
  void move(int x,int y){
    if(x0==x1 && y0==y1){
      this.x1=x;
      this.y1=y;
    }
    if( ypos == yp(y1) && xpos == xp(x1)){
        this.x0=this.x1;
        this.y0=this.y1;
    }else{ 
      if( xpos > xp(x1) ){xpos = (xpos - xp(x1))>vel ? xpos-vel : xp(x1) ;}
      if( xpos < xp(x1) ){xpos = (xp(x1) - xpos)>vel ? xpos+vel : xp(x1) ;}
      if( ypos > yp(y1) ){ypos = (ypos - yp(y1))>vel ? ypos-vel : yp(y1) ;}
      if( ypos < yp(y1) ){ypos = (yp(y1) - ypos)>vel ? ypos+vel : yp(y1) ;}
    }
  }
}

