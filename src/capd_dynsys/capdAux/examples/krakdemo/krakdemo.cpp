/// @addtogroup krakdemo
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file krakdemo.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <fstream>
#include "capd/krak/frame.h"
#include "capd/krak/noframe.h"
#define _low_level_

using namespace capd::krak;


void keyboard_test(void)
{
	SetFgCol(RED);
	SetBgCol(GREEN);
	UserMove um;

	rootFrame.Clear();
	rootFrame << At(0,0) << "Starting elementary keyboard/mouse test. To exit press ESC key";
	while(1)
	{
		int s=NO_KEY;
		while(NO_KEY==s) {GetUserMove(um);s=um.key;}
		rootFrame << At(2,0) << "Mouse : i=" << um.pxl.i << " j=" << um.pxl.j <<
		At(3,0) << " key=" << s << "   ";
		if (s==EscKey) break;
	}
}

void formatted_input_test(void)
{
	double x,y;
	Frame frm(rootFrame,40,50,95,95);
	frstring text;

	rootFrame.Clear();

	rootFrame << "Starting keyboard input test\n";
	while(1)
	{
		frm << At(0,0) << "Give me number x: ";
		frm >> x;
		frm << At(1,0) << "Give me number y: ";
		frm >> y;
		frm << At(2,0) << "x=" << x << " y=" << y << " x*y=" << x*y;

		frm << At(4,0) << "Write something.\n If you wish to exit, write exit: ";
		frm >> text;

		if(text == "exit\r") break;
		frm << At(6,0) << "You wrote: " << text;
		frm << At(7,0) << "Press any key.";
		waitBt();

		frm.Clear();
		frm.Bound();
	}
}

void graph_test(void)
{
	// test
	Frame *myFrm,*grFrm,*quitFrm;
	float wdw_size=10.0;
	int shape;
	capd::krak::Pxl pt;

	capd::krak::Rct r;
	int j;
	
	rootFrame.Clear();

	SetFgCol(BLUE);
//  grFrm=opdsFrm(0,25,50,99,-wdw_size,-wdw_size,wdw_size,wdw_size);
	grFrm=opdsFrm(0,25,40,50,-wdw_size,-wdw_size,wdw_size,wdw_size);
	myFrm=opdsFrm(0,0,99,99,-10.0,-10.0,10.0,10.0);
	quitFrm=opdsFrm(90,0,99,10,0.0,0.0,10.0,10.0);
	selFrm(quitFrm);
	drawFrm(quitFrm);
	gprintf_at(quitFrm,0,0,"QUIT");
	selFrm(myFrm);
	drawFrm(myFrm);
	gprintf_at(myFrm,0,0,
		"12345678901234567890\nabcdefghijABCDEFGHIJ\n");
	gprintf_at(myFrm,1,20,"klmnopqr\n");
	gprintf (myFrm, "Txt height/width = %d, %d\n\n", fontHght, fontWdth);
//	gprintf(myFrm,"ijklmnIJKLMNcs pqrsPQRS\n\n");
	gprintf(myFrm,"test=%7.3f n=%d",3.456,123);

	rootFrame << At(6,0) << "The next word should be in " << 
		colstring(YELLOW,GREEN," GREEN ") << " on YELLOW background";
	rootFrame << At(7,0) << "The last word should be in " << 
		FgColor(RED) << "RED" << FgColor(BLACK);
	rootFrame << At(8,0) << "This should be in black";
	
	SetFgCol(BLACK);

	gprintf_at(myFrm,10,0,"To exit, click in the QUIT window");

	drawFrm(grFrm);
	selFrm(myFrm);

	for (j=0;j<16;j++)
	{
		r.lti=500;
		r.ltj=fontHght*(j+4);
		r.rbi=515;
		r.rbj=fontHght*(j+5);
		rootFrame.boxFill(r.lti,r.ltj,r.rbi,r.rbj,j);
		SetFgCol(j);
		rootFrame << At(j+4,480/fontWdth) << j;
		rootFrame << At(j+4,520/fontWdth) << colorname[j];
	}

	for (j=0;j<16;j++)
	{
		int offset=17;
		r.lti=500;
		r.ltj=fontHght*(j+offset+4);
		r.rbi=515;
		r.rbj=fontHght*(j+offset+5);
		rootFrame.boxFill(r.lti,r.ltj,r.rbi,r.rbj,gray[j]);
		SetFgCol(gray[j]);
		rootFrame << At(j+offset+4,480/fontWdth) << j;
		rootFrame << At(j+offset+4,520/fontWdth) << colorname[gray[j]];
	}

  // Class Frame test
	Frame  shpFrm(rootFrame,0,50,40,99,-wdw_size,-wdw_size,wdw_size,wdw_size);
	shpFrm.Bound();
#if defined (WIN95) || defined (WXWIN)
	int prevSize = GetTextSize ();
	SetTextSize(16);
	shpFrm << FgColor(BLUE) 
		<< "The contents of this \nwindow so far works\n"
		"only in MS Win / wxWin" << FgColor(BLACK);
	shpFrm.ellipseFill(-3.0,-3.0, 3.0,-5.0,BROWN,VLINE_P);
	shpFrm.ellipse    (-3.0,-3.0, 3.0,-5.0,BLACK);

	int rgn[8]={ 10,410, 100,410,  55,460,  10,410};

//    rootFrame.arcFill(100,410, 200,450, 150,450, 100,400, BLUE,DHASH_P);
	rootFrame.arcFill(100,410, 200,450, 150,450, 100,400, ORANGE);
	rootFrame.arc    (100,410, 200,450, 100,400, 150,450, YELLOW);
	SetTextSize(prevSize);
  //  rootFrame.polygonFill(rgn,4,ORANGE,DHASH_P);
	rootFrame.SetFgColor(RED);
//    rootFrame.polygonFill(rgn,4,ORANGE);
//    FillRgn(rgn,4,SOLID_P,ORANGE);
	std::cout << "====<\n";
	SetFgCol(GREEN);
	FillRgn(rgn,4,SOLID_P,MAGENTA);
	std::cout << "====>\n";
	rootFrame.polygon(rgn,4,RED);
#else
	shpFrm << FgColor(BLUE) << "The contents of this window\n";
	shpFrm << "works only under MS Win and wxWin.\n";
	shpFrm << "Who can do it for X Win?";
#endif
  // end of class Frame test

	selFrm(grFrm);
	moveTo(0.0,5.0);
	lineTo(5.0,0.0);
	lineTo(0.0,-5.0);
	lineTo(-5.0,0.0);
	lineTo(0.0,5.0);
	grFrm->circle(0.0,0.0,10,RED);

	selFrm(grFrm);
	while(!Button());
	SetFgCol (BROWN);
	for(;;){
		while(!Button());
		GetMouse(&pt);
		if (MouseInFrm(quitFrm)) break;
		shape=1;
		if (pt.i > 300)
			shape = -1;
		if (shape>0)
		{
			Diamond(pt.i,pt.j,10);
		} else {
			if (shape<0) Crcl(pt.i,pt.j,10);
		}
	}
	clseFrm(grFrm);
	while(Button());
}

void frstringInOutTest(void)
{
	rootFrame.Clear();
	frstring alfa;
	alfa << 'X';
	alfa << -1961;
	alfa << '*';
	alfa << "-3.14";
	alfa << ' ';

	rootFrame << "Testing reading/writing from/to frstring:\n\n";
	rootFrame << "Contents of alfa is:\n";
	rootFrame << alfa << "\n";

	char c1,c2;
	int n;
	double d;

	rootFrame << "We read from alfa:\n";
	alfa >> c1 >> n >> c2 >> d;
	rootFrame << "Character:" << c1 << "\n";
	rootFrame << "Integer:" << n <<  "\n";
	rootFrame << "Character:" << c2 <<  "\n";
	rootFrame << "Double:" << d <<  "\n";
	waitBt();
}

#if defined (WIN95) || defined (WXWIN)
void krak_edu_test()
{
	int i,lti,ltj,rbi,rbj;

	clear();

/*
  frstring f;
  int pos;
  gettoken(cin,f);
  cin.seekg(pos);
  rootFrame << pos;
  waitBt();
*/
	rootFrame << FgColor(BLUE);
	rootFrame << At(0,0) << "12345678901234567890\nabcdefghijABCDEFGHIJ\n";
	rootFrame << At(6,0) << "The last word should be in ";
	rootFrame << FgColor(GREEN);
	rootFrame << "GREEN";
	rootFrame << FgColor(BLACK);

	rootFrame << At(10,0) << "To quit click outside the squares below";

	setBackgroundColor(YELLOW);
	drawText("XxxxxX",71,123,BLUE);
	draw(71,123);
	setBackgroundColor(WHITE);

	for (i=0;i<16;i++)
	{
		ltj=500;
		lti=fontHght*(i+4);
		rbj=515;
		rbi=fontHght*(i+5);
		jump(lti,ltj);
		boxFill(lti,ltj,rbi,rbj,i);
		rootFrame << FgColor(i);
		rootFrame << At(i+4,480/fontWdth) << i;
		rootFrame << At(i+4,520/fontWdth) << colorname[i];
	}
	rootFrame << FgColor (BROWN);

	box(200,0,500,200,RED);
	box(200,200,500,400,BLUE);

	// Note that initially screen coordinates are [0,1] x [0,1]
	boxFill(0.8,0.8, 0.9,0.9,YELLOW,DDOT_P);
//	boxFill(8.0,2.5, 9.5,3.5,YELLOW,DDOT_P);
//  box(8.0,2.5, 9.5,3.5,ORANGE);
 	ellipseFill(0.8,0.65, 0.9,0.75,BROWN,VLINE_P);
// 	ellipseFill(8.0,1.0, 9.5,2.0,BROWN,VLINE_P);
//  ellipse(8.0,1.0, 9.5,2.0,BLACK);
	circFill(0.85,0.55,0.05,BLUEGREEN,HLINE_P);
//	circFill(7.0,1.5,0.3,BLUEGREEN,HLINE_P);
//  circ(7.0,1.5,0.3,BLACK);

	int rgn[8]={410,410, 500,410, 455,460, 410,410};

	polygonFill(rgn,4,ORANGE,DHASH_P);
	polygon(rgn,4,RED);

	arcFill(300,410, 400,450, 350,450, 300,400, BLUE,DHASH_P);
	arc    (300,410, 400,450, 300,400, 350,450, YELLOW);

	while(!button());
	while(1){
		int row,col;
		while(!button());
		mouse(row,col);
		if (col>400 || row<200 || row>500) break;
		if (col>200){
			box(row-5,col-5,row+5,col+5,BLUE);
		}else{
			circ(row,col,10,RED);
		}
	}
	while(button());
}
#endif

int main(int , char* [])
{
	std::cout << "The test started...\n";
	openGW(760,580,WHITE,BLACK);

#if defined (WIN95) || defined (WXWIN)
	krak_edu_test();
#endif

	graph_test();
	keyboard_test();
	formatted_input_test();
	frstringInOutTest();

//	waitBt();
	closeGW();
	std::cout << "This is the end of the test.\n";
	return 0;
}

/// @}
