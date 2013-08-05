/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file wxWin.c
///
/// @author Pawel Pilarczyk
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by Pawel Pilarczyk.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// This is the Krak kernel implementation for wxWindows (wxWidgets) 2.5.2.
// Written in June 2004 by Pawel Pilarczyk (partially based on ms-win95.c).
// Adjusted for Unicode in December 2006.

// un-define words that get into conflict with the wxWin library
#undef begin
#undef end
#undef main
#undef UNIX

// overcome a problem with LineTo
#ifdef WIN95
#  undef LineTo
#else
#  define MWLineTo LineTo
#endif

// include the header files necessary to use the wxWin library
#include <wx/wx.h>
#include <wx/socket.h>
#include <wx/datetime.h>
#include <wx/colordlg.h>
#include <wx/imagpng.h>
#include <wx/imagjpeg.h>
#include <wx/imagtiff.h>

// include other header files
#include <math.h> // for "atan"
#include <cstdlib> // for "getenv" and "atoi"

// declare the main entry function with or without arguments
#ifdef NO_CMD_LINE_ARGS
   int mainEntry (void);
#else
   int mainEntry (int argc, char *argv []);
#endif

// the macro that translates the color numbers from the color palette;
// note that this is very inefficient - the color tables should probably be
// defined with integers, and not calculated every time the colors are used
#ifdef BLACKWHITE
#  define TRANSLATE_COLOR(c) (((c) == WHITE) ? (*wxWHITE) : (*wxBLACK))
#else
#  define TRANSLATE_COLOR(c) (wxColor (\
   (int) (255 * red_c [c % MAX_COLOR_NO]), \
   (int) (255 * green_c [c % MAX_COLOR_NO]), \
   (int) (255 * blue_c [c % MAX_COLOR_NO])))
#endif

// declare the main wxWindows application
namespace capd{
namespace krak{
namespace wxWin{
   class KrakApp;
}}}

DECLARE_APP (capd::krak::wxWin::KrakApp)

// open the capd::krak namespace
namespace capd{
namespace krak{
   // the width and the height of each letter in the font in use
   extern int fontWdth, fontHght;

   // the color of the background and of the foreground
   int c_bgcol, c_fgcol;

   // palette colors
   extern float red_c [MAX_PALETTE], green_c [MAX_PALETTE],
      blue_c [MAX_PALETTE];

   void set_pat ();
   void free_pat ();

// open the internal wxWin namespace
// in order to avoid name conflicts with other namespaces
namespace wxWin{

// --------------------------------------------------
// --------------------- Buffer ---------------------
// --------------------------------------------------
// This class implements a small integer buffer of the FIFO type
// to be used for storing keys pressed, for example.
// The access to the buffer is controlled against concurrent threads.

class Buffer
{
private:
   // buffer size
   int size;

   // the cyclic buffer itself
   int *buf;

   // reading position
   int read;

   // writing position
   int write;

   // a lock to avoid concurrent access to the buffer
   wxCriticalSection s;

public:
   // constructor
   Buffer (int _size = 16): size (_size), read (0), write (0)
   {
      buf = new int [size];
      return;
   }

   // destructor
   ~Buffer ()
   {
      delete [] buf;
      return;
   }

   // add an entry to the buffer; return true iff successful
   bool add (int x)
   {
      wxCriticalSectionLocker locker (s);
      int next = write + 1;
      if (next >= size)
         next = 0;
      if (next == read)
         return false;
      buf [write] = x;
      write = next;
      return true;
   }

   // get an entry from the buffer; return -1 if empty
   int get ()
   {
      if (read == write)
         return -1;
      wxCriticalSectionLocker locker (s);
      int x = buf [read];
      int next = read + 1;
      if (next >= size)
         next = 0;
      read = next;
      return x;
   }

   // is the buffer empty?
   bool empty ()
   {
      return (read == write);
   }

}; /* class Buffer */


// --------------------------------------------------
// ---------------- Useful functions ----------------
// --------------------------------------------------

inline void paintAddedAreas (wxDC &dc, wxBrush &brush,
   wxCoord prevWidth, wxCoord prevHeight,
   wxCoord newWidth, wxCoord newHeight)
// Paint areas added to the previous picture while resizing.
{
   if ((newWidth <= prevWidth) && (newHeight <= prevHeight))
      return;
   //dc. BeginDrawing ();
   dc. SetPen (*wxTRANSPARENT_PEN);
   dc. SetBrush (brush);
   if (newWidth > prevWidth)
      dc. DrawRectangle (prevWidth, 0, newWidth - prevWidth,
         newHeight);
   if (newHeight > prevHeight)
      dc. DrawRectangle (0, prevHeight,
         (newWidth > prevWidth) ? prevWidth : newWidth,
         newHeight - prevHeight);
   //dc. EndDrawing ();
   return;
} /* paintAddedAreas */


// --------------------------------------------------
// ---------------- Global variables ----------------
// --------------------------------------------------
// Here are a couple of global variables gathered.
// These variables are used by the Krak kernel functions
// and serve as a communication tool between the window frame
// and the main program thread.


// is the mouse button pressed?
static bool mouseButtonDown = false;

// the current mouse position
static int mouseX = 0, mouseY = 0;

// a buffer for captured keys
static Buffer keyBuffer;

// patterns used for brushes (see: set_pat and free_pat below)
static wxBitmap *hbmp_pat [MAX_PATTERN_NO];
static wxBrush *hbmp_brush [MAX_PATTERN_NO];

// the current point (for drawing lines and plotting text)
static int current_x = 0, current_y = 0;

// the current font size (in points)
static int fontSize = 10;

// the main program's stop-watch
static wxStopWatch *stopWatch = (wxStopWatch *) NULL;

// the default status text
const wxChar *defaultStatusText =
	wxT("This application uses Krak5 and wxWidgets.");

// the critical section lock used for operations on the memory bitmap
static wxCriticalSection memSection;

// should the drawing be updated on every key/mouse check? after drawing?
static bool refreshOn = true, updateKey = false, updateDraw = false;

// show the information about mouse position and keys pressed?
static bool showInfo = false;


// --------------------------------------------------
// ------------------- Krak Frame -------------------
// --------------------------------------------------

class KrakFrame: public wxFrame
{
private:
   // screen copy memory buffer management
   void allocateMemory ();
   void releaseMemory ();

   // the background brush (used for painting areas added on resizing)
   wxBrush *bgBrush;

   // the current size of the client painting (updated on resize)
   wxCoord width, height;

   // the size of the minimal painting area kept in the memory
   wxCoord memWidth, memHeight;

   // the initial size of the entire window (including borders etc.)
   wxCoord initialWidth, initialHeight;

public:
   // a bitmap copy of the screen (for refreshing and saving)
   wxBitmap *bmpMem;
   wxMemoryDC *dcMem;

   // frame constructor and destructor
   KrakFrame (const wxString &title, const wxPoint &pos,
      const wxSize &clientSize, wxColor bgColor);
   ~KrakFrame ();

   // menu events handling
   void Save (const wxChar *files, wxBitmapType type);
   void OnSaveBMP (wxCommandEvent& event);
   void OnSavePNG (wxCommandEvent& event);
   void OnSaveJPG (wxCommandEvent& event);
   void OnSaveTIF (wxCommandEvent& event);
   void OnQuit (wxCommandEvent& event);

   void OnFixedSize (wxCommandEvent& event);
   void OnInfo (wxCommandEvent& event);
   void OnUpdateKey (wxCommandEvent& event);
   void OnUpdateDraw (wxCommandEvent& event);
   void OnRefresh (wxCommandEvent& event);

   void OnInitialSize (wxCommandEvent& event);
   void OnClear (wxCommandEvent& event);
   void OnMisbehave (wxCommandEvent& event);

   void OnAbout (wxCommandEvent& event);

   // mouse and keyboard events handling
   void showMouseInfo ();
   void OnMouseDown (wxMouseEvent& event);
   void OnMouseUp (wxMouseEvent& event);
   void OnMouseMove (wxMouseEvent& event);
   void OnChar (wxKeyEvent& event);

   // other events handling
   void OnSize (wxSizeEvent& event);
   void OnPaint (wxPaintEvent& event);
   void OnClose (wxCloseEvent& event);

   DECLARE_EVENT_TABLE ()

}; /* class KrakFrame */


// --------------------------------------------------
// ---------------- Krak Application ----------------
// --------------------------------------------------

KrakFrame *krakFrame = (KrakFrame *) NULL;

class KrakApp: public wxApp
{
public:
   virtual bool OnInit ();

private:
   // local variables; to do: release them upon program's exit
   wxMutex *m_mutex;
   wxCondition *m_condition;
   wxMutex *m_done;

}; /* class KrakApp */

// --------------------------------------------------

enum
{
   ID_Quit = 2000,
   ID_SaveBMP,
   ID_SavePNG,
   ID_SaveJPG,
   ID_SaveTIF,
   ID_FixedSize,
   ID_Info,
   ID_UpdateKey,
   ID_UpdateDraw,
   ID_Refresh,
   ID_InitialSize,
   ID_Clear,
   ID_Misbehave,
   ID_About
};

BEGIN_EVENT_TABLE (KrakFrame, wxFrame)
   // menu events
   EVT_MENU (ID_SaveBMP, KrakFrame::OnSaveBMP)
   EVT_MENU (ID_SavePNG, KrakFrame::OnSavePNG)
   EVT_MENU (ID_SaveJPG, KrakFrame::OnSaveJPG)
   EVT_MENU (ID_SaveTIF, KrakFrame::OnSaveTIF)
   EVT_MENU (ID_Quit, KrakFrame::OnQuit)
   EVT_MENU (ID_FixedSize, KrakFrame::OnFixedSize)
   EVT_MENU (ID_Info, KrakFrame::OnInfo)
   EVT_MENU (ID_UpdateKey, KrakFrame::OnUpdateKey)
   EVT_MENU (ID_UpdateDraw, KrakFrame::OnUpdateDraw)
   EVT_MENU (ID_Refresh, KrakFrame::OnRefresh)
   EVT_MENU (ID_InitialSize, KrakFrame::OnInitialSize)
   EVT_MENU (ID_Clear, KrakFrame::OnClear)
   EVT_MENU (ID_Misbehave, KrakFrame::OnMisbehave)
   EVT_MENU (ID_About, KrakFrame::OnAbout)

   // mouse and keyboard events
#if !defined (__WXGTK__)
   EVT_CHAR (KrakFrame::OnChar)
#endif
   EVT_LEFT_DOWN (KrakFrame::OnMouseDown)
   EVT_LEFT_UP (KrakFrame::OnMouseUp)
   EVT_MOTION (KrakFrame::OnMouseMove)

   // various events
   EVT_SIZE (KrakFrame::OnSize)
   EVT_PAINT (KrakFrame::OnPaint)
   EVT_CLOSE (KrakFrame::OnClose)
END_EVENT_TABLE ()


// --------------------------------------------------
// ------------------- Krak Frame -------------------
// --------------------------------------------------
// This is the implementation of the KrakFrame class methods.

KrakFrame::KrakFrame (const wxString &title, const wxPoint& pos,
   const wxSize &clientSize, wxColor bgColor):
   wxFrame ((wxFrame *) NULL, -1, title, pos, clientSize),
   bgBrush ((wxBrush *) NULL),
   bmpMem ((wxBitmap *) NULL), dcMem ((wxMemoryDC *) NULL)
{
   // the status bar
   CreateStatusBar ();
   SetStatusText (defaultStatusText);

   // the File menu
   wxMenu *menuFile = new wxMenu;
   menuFile -> Append (ID_SaveBMP, wxT("&Save BMP"),
      wxT("Save the contents of the window to a Windows BMP file"));
#if wxUSE_LIBPNG
   menuFile -> Append (ID_SavePNG, wxT("Save &PNG"),
      wxT("Save the contents of the window to a PNG bitmap file"));
#endif
#if wxUSE_LIBJPEG
   menuFile -> Append (ID_SaveJPG, wxT("Save &JPEG"),
      wxT("Save the contents of the window to a JPEG file"));
#endif
#if wxUSE_LIBTIFF
   menuFile -> Append (ID_SaveTIF, wxT("Save &TIFF"),
      wxT("Save the contents of the window to a TIFF file"));
#endif
   menuFile -> AppendSeparator ();
   menuFile -> Append (ID_Quit, wxT("E&xit"),
      wxT("Interrupt the program execution"));

   // the Options menu
   wxMenu *menuOptions = new wxMenu;
   menuOptions -> AppendCheckItem (ID_Info, wxT("&Mouse/key info"),
      wxT("Toggle displaying mouse position ")
      wxT("and pressed keys in the status bar"));
   menuOptions -> Check (ID_Info, showInfo);
#if defined (__WXGTK__)
   menuOptions -> AppendCheckItem (ID_UpdateKey, wxT("&Update on mouse/key"),
      wxT("Update the screen on every mouse/keyboard check"));
   menuOptions -> Check (ID_UpdateKey, updateKey);
   menuOptions -> AppendCheckItem (ID_UpdateDraw, wxT("Update on &drawing"),
      wxT("Update the screen every time anything is drawn on it"));
   menuOptions -> Check (ID_UpdateDraw, updateDraw);
#else
   menuOptions -> AppendCheckItem (ID_FixedSize, wxT("&Lock size"),
      wxT("Lock the current size of the window"));
#endif
   menuOptions -> AppendCheckItem (ID_Refresh, wxT("&Refresh"),
      wxT("Toggle screen refreshing (don't turn it off!)"));

   // the Window menu
   wxMenu *menuWindow = new wxMenu;
   menuWindow -> Append (ID_Clear, wxT("&Clear contents"),
      wxT("Clear the contents of the window"));
   menuWindow -> Append (ID_InitialSize, wxT("&Initial size"),
      wxT("Return to the initial size of the window ")
      wxT("(does nothing if the size is locked)"));
   menuWindow -> Append (ID_Misbehave, wxT("&Misbehave"),
      wxT("Misbehave!"));

   // the Help menu
   wxMenu *menuHelp = new wxMenu;
   menuHelp -> Append (ID_About, wxT("&About..."),
      wxT("About... what?"));

   // the menu bar
   wxMenuBar *menuBar = new wxMenuBar;
   menuBar -> Append (menuFile, wxT("&File"));
   menuBar -> Append (menuOptions, wxT("&Options"));
   menuBar -> Append (menuWindow, wxT("&Window"));
   menuBar -> Append (menuHelp, wxT("&Help"));
   SetMenuBar (menuBar);

   // check the current size of the painting area and adjust window size
   GetClientSize (&width, &height);
   initialWidth = 2 * clientSize. x - width;
   initialHeight = 2 * clientSize. y - height;
   if ((width != clientSize. x) || (height != clientSize. y))
      SetSize (pos. x, pos. y, initialWidth, initialHeight);
   GetClientSize (&width, &height);

   // remember the size requested by the OpenGraphics function
   // as the minimal size of the memory buffer in use
   memWidth = clientSize. x;
   memHeight = clientSize. y;

   // create the default background brush
   bgBrush = new wxBrush (bgColor, wxSOLID);

   // clear the initial screen with the requested background color
   wxClientDC dc (this);
  // dc. BeginDrawing ();
   dc. SetBackground (*bgBrush);
   dc. Clear ();
   //dc. EndDrawing ();

   // show the frame
   Show (TRUE);

   // turn on the screen refresh support if necessary
#ifdef _REFRESH_
   if (refreshOn)
   {
      allocateMemory ();
      menuOptions -> Check (ID_Refresh, true);
   }
#endif

   return;
} /* KrakFrame::KrakFrame */

KrakFrame::~KrakFrame ()
{
   memSection. Enter ();
   releaseMemory ();
   memSection. Leave ();
   return;
} /* KrakFrame::~KrakFrame */

void KrakFrame::allocateMemory ()
{
   // release memory if already allocated
   if (dcMem || bmpMem)
      releaseMemory ();

   // create the memory bitmap and its device context
   if (memWidth <= 0)
      memWidth = width;
   if (memHeight <= 0)
      memHeight = height;
   bmpMem = new wxBitmap ((memWidth > width) ? memWidth : width,
      (memHeight > height) ? memHeight : height);
   dcMem = new wxMemoryDC;
   dcMem -> SelectObject (*bmpMem);

   // copy copy the screen and paint uninitialized areas
   wxClientDC dc (this);
   dcMem -> Blit (0, 0, width, height, &dc, 0, 0);
   paintAddedAreas (*dcMem, *bgBrush, width, height,
      memWidth, memHeight);

   return;
} /* KrakFrame::allocateMemory */

void KrakFrame::releaseMemory ()
{
   if (dcMem)
   {
      dcMem -> SelectObject (wxNullBitmap);
      delete dcMem;
      dcMem = (wxMemoryDC *) NULL;
   }
   if (bmpMem)
   {
      delete bmpMem;
      bmpMem = (wxBitmap *) NULL;
   }
   return;
} /* KrakFrame::releaseMemory */

void KrakFrame::Save (const wxChar *files, wxBitmapType type)
{
   // from the wxWindows documentation: "modal dialogs are one of the
   // very few examples of wxWindow-derived objects which may be
   // created on the stack and not on the heap"
   wxFileDialog dlg (this, wxT("Save bitmap"), wxT(""),
      wxT(""), files, wxFD_SAVE | wxFD_OVERWRITE_PROMPT);
   if (dlg. ShowModal () == wxID_OK)
   {
      memSection. Enter ();
      bool release = !bmpMem;
      if (!bmpMem)
         allocateMemory ();
      bool result = bmpMem -> SaveFile (dlg. GetPath (), type);
      if (release)
         releaseMemory ();
      memSection. Leave ();

      if (!result)
         wxMessageBox (wxT("Unable to save - an error occurred."),
            wxT("Not saved"), wxOK, this);
   }

   return;
} /* KrakFrame::Save */

void KrakFrame::OnSaveBMP (wxCommandEvent& WXUNUSED (event))
{
   Save (wxT("Bitmap files (*.bmp)|*.bmp|All files (*.*)|*.*"),
      wxBITMAP_TYPE_BMP);
   return;
} /* KrakFrame::OnSaveBMP */

void KrakFrame::OnSavePNG (wxCommandEvent& WXUNUSED (event))
{
   static bool added = false;
   if (!added)
   {
      #if wxUSE_LIBPNG
      wxImage::AddHandler (new wxPNGHandler);
      #endif
      added = true;
   }
   Save (wxT("PNG bitmap files (*.png)|*.png|All files (*.*)|*.*"),
      wxBITMAP_TYPE_PNG);
   return;
} /* KrakFrame::OnSavePNG */

void KrakFrame::OnSaveJPG (wxCommandEvent& WXUNUSED (event))
{
   static bool added = false;
   if (!added)
   {
      #if wxUSE_LIBJPEG
      wxImage::AddHandler (new wxJPEGHandler);
      #endif
      added = true;
   }
   Save (wxT("JPEG bitmap files (*.jpg)|*.jpg|All files (*.*)|*.*"),
      wxBITMAP_TYPE_JPEG);
   return;
} /* KrakFrame::OnSaveJPG */

void KrakFrame::OnSaveTIF (wxCommandEvent& WXUNUSED (event))
{
   static bool added = false;
   if (!added)
   {
      #if wxUSE_LIBTIFF
      wxImage::AddHandler (new wxTIFFHandler);
      #endif
      added = true;
   }
   Save (wxT("TIFF bitmap files (*.tif)|*.tif|All files (*.*)|*.*"),
      wxBITMAP_TYPE_TIF);
   return;
} /* KrakFrame::OnSaveTIF */

void KrakFrame::OnFixedSize (wxCommandEvent& event)
{
   if (event. IsChecked ())
   {
      int width = -1, height = -1;
      GetSize (&width, &height);
      SetSizeHints (width, height, width, height);
   }
   else
      SetSizeHints (-1, -1);
   return;
} /* KrakFrame::OnFixedSize */

void KrakFrame::OnInfo (wxCommandEvent& event)
{
   if (event. IsChecked ())
      showInfo = true;
   else
   {
      showInfo = false;
      SetStatusText (defaultStatusText);
   }
   return;
} /* KrakFrame::OnInfo */

void KrakFrame::OnUpdateKey (wxCommandEvent& event)
{
   if (event. IsChecked ())
      updateKey = true;
   else
      updateKey = false;
   return;
} /* KrakFrame::OnUpdateKey */

void KrakFrame::OnUpdateDraw (wxCommandEvent& event)
{
   if (event. IsChecked ())
      updateDraw = true;
   else
      updateDraw = false;
   return;
} /* KrakFrame::OnUpdateDraw */

void KrakFrame::OnRefresh (wxCommandEvent& event)
{
   memSection. Enter ();
   if (event. IsChecked ())
      allocateMemory ();
   else
      releaseMemory ();
   memSection. Leave ();
   return;
} /* KrakFrame::OnRefresh */

void KrakFrame::OnInitialSize (wxCommandEvent& WXUNUSED (event))
{
   int xPos = -1, yPos = -1;
   GetPosition (&xPos, &yPos);
   SetSize (xPos, yPos, initialWidth, initialHeight);
   return;
} /* KrakFrame::OnInitialSize */

void KrakFrame::OnClear (wxCommandEvent& WXUNUSED (event))
{
   wxClientDC dc (this);
 //  dc. BeginDrawing ();
   dc. SetBackground (*bgBrush);
   dc. Clear ();
  // dc. EndDrawing ();

   memSection. Enter ();
   if (dcMem)
   {
     // dcMem -> BeginDrawing ();
      dcMem -> SetBackground (*bgBrush);
      dcMem -> Clear ();
     // dcMem -> EndDrawing ();
   }
   memSection. Leave ();
   return;
} /* KrakFrame::OnClear */

void KrakFrame::OnMisbehave (wxCommandEvent& WXUNUSED (event))
{
   wxMessageBox(wxT("NO WAY! This window should not misbehave! ")
      wxT("But if it does, you should complain to ")
      wxT("Pawel Pilarczyk at http://www.PawelPilarczyk.com/."),
      wxT("Misbehave"), wxOK | wxICON_INFORMATION, this);
   return;
} /* KrakFrame::OnMisbehave */

void KrakFrame::OnAbout (wxCommandEvent& WXUNUSED (event))
{
   wxMessageBox(wxT("The Krak5 kernel for wxWindows (wxWidgets) ")
      wxT("was programmed in June 2004 by Pawel Pilarczyk."),
      wxT("About the program"), wxOK | wxICON_INFORMATION, this);
   return;
} /* KrakFrame::OnAbout */

// --------------------------------------------------

void KrakFrame::OnMouseDown (wxMouseEvent& event)
{
   mouseButtonDown = true;
   wxPoint pos = event. GetPosition ();
   mouseX = pos. x;
   mouseY = pos. y;

   if (!showInfo)
      return;
   wxString msg;
   msg. Printf (wxT("Mouse: %d, %d. Button pressed."), mouseX, mouseY);
   SetStatusText (msg);
   return;
} /* KrakFrame::OnMouseDown */

void KrakFrame::OnMouseUp (wxMouseEvent& event)
{
   mouseButtonDown = false;
   wxPoint pos = event. GetPosition ();
   mouseX = pos. x;
   mouseY = pos. y;

   if (!showInfo)
      return;
   wxString msg;
   msg. Printf (wxT("Mouse: %d, %d. Button released."), mouseX, mouseY);
   SetStatusText (msg);
   return;
} /* KrakFrame::OnMouseUp */

void KrakFrame::OnMouseMove (wxMouseEvent& event)
{
   wxPoint pos = event. GetPosition ();
   mouseX = pos. x;
   mouseY = pos. y;
   mouseButtonDown = event. LeftIsDown ();

   if (!showInfo)
      return;
   wxString msg;
   msg. Printf (wxT("Mouse: %d, %d. Button is %s."), mouseX, mouseY,
      mouseButtonDown ? wxT("down") : wxT("up"));
   SetStatusText (msg);
   return;
} /* KrakFrame::OnMouseMove */

void KrakFrame::OnChar (wxKeyEvent& event)
{
   // interprete the key in the menu or by the system
   event. Skip ();

   // get the key code
   int ch = event. GetKeyCode ();

   if (showInfo)
   {
      wxString msg;
      msg. Printf (wxT("Key %d ('%c') pressed."), ch, (wxChar) ch);
      SetStatusText (msg);
   }

   // add the key to the buffer and beep if the buffer is full
   if (!keyBuffer. add (ch))
      wxBell ();

   return;
} /* KrakFrame::OnChar */

// --------------------------------------------------

void KrakFrame::OnSize (wxSizeEvent& event)
{
   // of no background brush is allocated, the frame is not
   // initialized yet, so no reaction to the size event is necessary
   if (!bgBrush)
      return;

   memSection. Enter ();
   int newWidth, newHeight;
   GetClientSize (&newWidth, &newHeight);

   // if the area got enlarged, paint added parts with background color
   wxClientDC dc (this);
   paintAddedAreas (dc, *bgBrush, width, height, newWidth, newHeight);

   // allocate a new memory bitmap if it is in use and either the width
   // or height changed, and either the previous one or the new one
   // exceeds the minimal bitmap size (sorry for the complex condition!)
   if (dcMem &&
      (((newWidth != width) &&
      ((width > memWidth) || (newWidth > memWidth))) ||
      ((newHeight != height) &&
      ((height > memHeight) || (newHeight > memHeight)))))
   {
      wxCoord widthBmp = (newWidth > memWidth) ? newWidth :
         memWidth;
      wxCoord heightBmp = (newHeight > memHeight) ? newHeight :
         memHeight;
      wxBitmap *bmpMem1 = new wxBitmap (widthBmp, heightBmp);
      wxMemoryDC *dcMem1 = new wxMemoryDC;
      dcMem1 -> SelectObject (*bmpMem1);
      dcMem1 -> Blit (0, 0, widthBmp, heightBmp, dcMem, 0, 0);
      delete dcMem;
      delete bmpMem;
      dcMem = dcMem1;
      bmpMem = bmpMem1;
      paintAddedAreas (*dcMem, *bgBrush, memWidth, memHeight,
         widthBmp, heightBmp);
   }

   // remember the new size
   width = newWidth;
   height = newHeight;

   memSection. Leave ();
   return;
} /* KrakFrame::OnSize */

void KrakFrame::OnPaint (wxPaintEvent& WXUNUSED (event))
{
   wxPaintDC dc (this);
   memSection. Enter ();
   if (dcMem)
      dc. Blit (0, 0, width, height, dcMem, 0, 0);
   memSection. Leave ();
   if (!showInfo)
      return;

   static int counter = 0;
   wxString msg;
   msg. Printf (wxT("Repaint: %d"), ++ counter);
   SetStatusText (msg);
   return;
} /* KrakFrame::OnPaint */


#if defined (__WXGTK__)
// --------------------------------------------------
// ------------------- Krak Panel -------------------
// --------------------------------------------------
// This panel is used to intercept the keyboard focus
// under GTK, because wxFrame is incapable of this.

class KrakPanel: public wxPanel
{
public:
   KrakPanel (wxWindow *parent): wxPanel (parent, -1,
      wxPoint (0, 0), wxSize (0, 0)) {}

   void OnChar (wxKeyEvent &event)
   {
      krakFrame -> OnChar (event);
      return;
   }

   DECLARE_EVENT_TABLE ()

}; /* class KrakPanel */

BEGIN_EVENT_TABLE (KrakPanel, wxPanel)
   EVT_CHAR (KrakPanel::OnChar)
END_EVENT_TABLE ()

KrakPanel *krakPanel = (KrakPanel *) NULL;
#endif // defined (__WXGTK__)


// --------------------------------------------------
// ------------------ Krak Thread -------------------
// --------------------------------------------------
// This thread is detached from the main thread to run the program,
// while the main thread serves the graphics user interface.

class KrakThread: public wxThread
{
public:
   // the parameters of the graphics window that has to be created
   wxCoord x, y, width, height;
   wxColor bgColor;

   // set the following to "true" by the thread to request
   // that the main thread opens a graphics window
   static bool openGraphics;

   // the following mutex is unlocked by the main thread
   // after the graphics window has been opened
   wxMutex &m_done;

   // a condition at which the main thread is waiting to open the
   // graphics window or to quit the program if openGraphics == false
   wxCondition &m_condition;
   wxMutex &m_mutex;

   // the constructor of the thread
   KrakThread (wxMutex &mutex, wxCondition &condition, wxMutex &done,
      wxThreadKind kind = wxTHREAD_DETACHED): wxThread (kind),
      m_done (done), m_condition (condition), m_mutex (mutex)
   {
      return;
   }

   // the main entry of the thread
   ExitCode Entry ()
   {
      // run the main function
      #ifdef NO_CMD_LINE_ARGS
      mainEntry ();
      #else
      int argc = wxGetApp (). argc;
      char **argv = new char * [argc];
      wxChar **wxArgv = wxGetApp (). argv;
      for (int i = 0; i < argc; ++ i)
      {
         wxString arg (wxArgv [i]);
         argv [i] = new char [arg. Len () + 1];
         std::strcpy (argv [i], arg. mb_str ());
      }

      mainEntry (argc, argv);
      #endif

      // close the frame and free allocated patterns if necessary
      if (krakFrame)
      {
         wxMutexGuiEnter ();
         krakFrame -> Destroy ();
         krakFrame = (KrakFrame *) NULL;
         wxMutexGuiLeave ();
         free_pat ();
         #ifdef __WXGTK__
         Yield ();
         wxGetApp (). ExitMainLoop ();
         #endif
      }

      // if no graphics was used, ask the main thread to exit
      else
      {
         wxMutexLocker lock (m_mutex);
         m_condition. Broadcast ();
      }

      return 0;
   }

}; /* class KrakThread */

// the global thread variable to remember whether the thread wants to open
// a graphics window
bool KrakThread::openGraphics = false;

KrakThread *krakThread = (KrakThread *) NULL;

// yield the Krak thread to update graphics appearing on the screen
inline void yield ()
{
   krakThread -> Yield ();
   return;
} /* yield */

// --------------------------------------------------

static bool askInterrupt (KrakFrame *frame)
{
   wxMessageDialog *dlg = new wxMessageDialog (frame,
      wxT("This will interrupt the program.\n")
      wxT("Are you sure you really want this?"),
      wxT("Krak Interrupt"),
      wxYES_NO | wxNO_DEFAULT | wxICON_EXCLAMATION);
   int result = dlg -> ShowModal ();
   dlg -> Destroy ();
   return (result != wxID_NO);
} /* askInterrupt */

void KrakFrame::OnQuit (wxCommandEvent& WXUNUSED (event))
{
   if (askInterrupt (this))
   {
      krakThread -> Kill ();
      Destroy ();
   }
   return;
} /* KrakFrame::OnQuit */

void KrakFrame::OnClose (wxCloseEvent& event)
{
   if (event. CanVeto ())
   {
      if (askInterrupt (this))
      {
         krakThread -> Kill ();
         Destroy ();
      }
      else
      {
         event. Veto ();
      }
   }
   else
   {
      krakThread -> Kill ();
      Destroy ();
   }
   return;
} /* KrakFrame::OnClose */

// --------------------------------------------------
// ---------------- Krak Application ----------------
// --------------------------------------------------

bool KrakApp::OnInit ()
// This function is called at the application start.
{
   // the initialization of the sockets event processing, as suggested
   // at http://www.litwindow.com/Knowhow/wxSocket/wxsocket.html
   wxSocketBase::Initialize ();

#ifdef __WXGTK__
   // set the correct locale for reading the real numbers
   setlocale (LC_NUMERIC, "C");
#endif

   // set the initial values of refreshOn, updateKey,
   // updateDraw and showInfo upon request
   const char *updateSetting = getenv ("WXREFRESH");
   if (updateSetting && (updateSetting [0] >= '0') &&
      (updateSetting [0] <= '9'))
   {
      int flags = atoi (updateSetting);
      refreshOn = flags & 0x01;
      updateDraw = flags & 0x02;
      updateKey = flags & 0x04;
      showInfo = flags & 0x08;
   }

   // create the program's stop-watch (don't delete it later...)
   stopWatch = new wxStopWatch ();

   // prepare a condition at which to wait before opening graphics
   m_mutex = new wxMutex;
   m_condition = new wxCondition (*m_mutex);
   m_mutex -> Lock ();

   // prepare a mutex at which the thread waits for a graphics window
   m_done = new wxMutex;
   m_done -> Lock ();

   // create the Krak thread
   krakThread = new KrakThread (*m_mutex, *m_condition, *m_done);
   krakThread -> Create ();
   krakThread -> Run ();

   // wait until the thread wants to open a graphics window
   m_condition -> Wait ();

   // shut down if the thread didn't use graphics
   if (!KrakThread::openGraphics)
      return FALSE;

   // open a graphics window as requested by the thread
   krakFrame = new KrakFrame (wxT("Krak in wxWindows"),
      wxPoint (krakThread -> x, krakThread -> y),
      wxSize (krakThread -> width, krakThread -> height),
      krakThread -> bgColor);
   SetTopWindow (krakFrame);

#ifdef __WXGTK__
   // create a panel which will receive keyboard events and transfer
   // them back to krakFrame; this is necessary if GTK is used
   krakPanel = new KrakPanel (krakFrame);
   krakPanel -> SetFocus ();
#endif

   // let the thread continue with the new graphics window
   m_done -> Unlock ();

   return TRUE; // return FALSE iff stop the program
} /* KrakApp::OnInit */


// --------------------------------------------------

inline void drawingFinished ()
{
#if defined (__WXGTK__)
   // this makes drawing a lot slower, but otherwise you must
   // move your mouse or tap your keyboard for the drawing
   // to actually appear on the screen
   if (updateDraw)
      krakPanel -> Refresh ();
#endif
   return;
} /* drawingFinished */

inline void keyWasChecked ()
{
#if defined (__WXGTK__)
   // this makes drawing a lot slower, but otherwise you must
   // move your mouse or tap your keyboard for the drawing
   // to actually appear on the screen
   if (updateKey)
   {
      wxMutexGuiEnter ();
      krakPanel -> Refresh ();
      wxMutexGuiLeave ();
   }
#endif
   return;
} /* keyWasChecked */


} // the end of the wxWin namespace

using namespace wxWin;


// --------------------------------------------------
// ---------------- Kernel Functions ----------------
// --------------------------------------------------

void set_pat ()
// Allocate patterns used for drawing filled entities.
{
   for (int i = 0; i < MAX_PATTERN_NO; i ++)
   {
      #if defined (__WXGTK__) || wxCHECK_VERSION (2, 8, 0)
      for (int j = 0; j < 8; j ++)
         patt_pntr [i] [j] = ~patt_pntr [i] [j];
      #endif
      // create a bitmap from the XBM image data
      hbmp_pat [i] = new wxBitmap ((const char *) (patt_pntr [i]),
         8, 8, 1);
      // make a mask from this bitmap
      wxMask *mask = new wxMask (*(hbmp_pat [i]));
      // set this mask for the bitmap itself
      hbmp_pat [i] -> SetMask (mask);
      // define a brush based on this bitmask
      hbmp_brush [i] = new wxBrush (*(hbmp_pat [i]));
   }
   return;
} /* set_pat */

void free_pat ()
// Free the memory allocated for the patterns.
{
   int i;

   for (i = 0; i < MAX_PATTERN_NO; i ++)
   {
      if (hbmp_pat [i])
         delete hbmp_pat [i];
      hbmp_pat [i] = (wxBitmap *) NULL;
      if (hbmp_brush [i])
         delete hbmp_pat [i];
      hbmp_brush [i] = (wxBrush *) NULL;
   }
   return;
} /* free_pat */

int GetKey ()
{
   keyWasChecked ();
   if (keyBuffer. empty ())
      return NO_KEY;
   else
      return keyBuffer. get ();
} /* GetKey */

void GetMouse (Pxl *pxl)
{
   keyWasChecked ();
   pxl -> i = mouseX;
   pxl -> j = mouseY;
   return;
} /* GetMouse */

int Button ()
{
   keyWasChecked ();
   return (int) mouseButtonDown;
} /* Button */

void Beep (int, int) // freq, time
{
   wxBell ();
   yield ();
   return;
} /* Beep */

inline void PlotDot (wxDC &dc, wxPen &pen, int i, int j)
{
  // dc. BeginDrawing ();
   dc. SetMapMode (wxMM_TEXT);
   dc. SetPen (pen);
   dc. DrawPoint (i, j);
   dc. SetPen (wxNullPen);
 //  dc. EndDrawing ();
   return;
} /* PlotDot */

void PlotDot (int i, int j)
{
   if (!krakFrame)
      return;
   wxMutexGuiEnter ();

   wxPen pen (TRANSLATE_COLOR (c_fgcol), 1, wxSOLID);

   wxClientDC dc (krakFrame);
   PlotDot (dc, pen, i, j);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      PlotDot (*(krakFrame -> dcMem), pen, i, j);
   memSection. Leave ();

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* PlotDot */

void MoveTo (int i, int j)
{
   current_x = i;
   current_y = j;

   yield ();
   return;
} /* MoveTo */

inline void MWLineTo (wxDC &dc, wxPen &pen, int i, int j)
{
   //dc. BeginDrawing ();
   dc. SetMapMode (wxMM_TEXT);
   dc. SetPen (pen);
   dc. DrawLine (current_x, current_y, i, j);
   dc. SetPen (wxNullPen);
  // dc. EndDrawing ();
   return;
} /* MWLineTo */

void MWLineTo (int i, int j)
{
   if (!krakFrame)
      return;
   wxMutexGuiEnter ();

   wxPen pen (TRANSLATE_COLOR (c_fgcol), 1, wxSOLID);

   wxClientDC dc (krakFrame);
   MWLineTo (dc, pen, i, j);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      MWLineTo (*(krakFrame -> dcMem), pen, i, j);
   memSection. Leave ();

   current_x = i;
   current_y = j;

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* MWLineTo */

inline void Crcl (wxDC &dc, wxPen &pen, int i, int j, int r)
// Draw an empty circle on the given DC with the given pen.
{
 //  dc. BeginDrawing ();
   dc. SetMapMode (wxMM_TEXT);
   dc. SetPen (pen);
   dc. SetBrush (*wxTRANSPARENT_BRUSH);
   dc. DrawCircle (i, j, r);
   dc. SetPen (wxNullPen);
  // dc. EndDrawing ();
   return;
} /* Crcl */

void Crcl (int i, int j, int r)
// Draw an empty circle.
{
   if (!krakFrame)
      return;
   wxMutexGuiEnter ();

   wxPen pen (TRANSLATE_COLOR (c_fgcol), 1, wxSOLID);

   wxClientDC dc (krakFrame);
   Crcl (dc, pen, i, j, r);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      Crcl (*(krakFrame -> dcMem), pen, i, j, r);
   memSection. Leave ();

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* Crcl */

inline void FillRct (wxDC &dc, Rct *r, int pattNr, int colNr)
// Draw a filled rectangle on the given DC.
{
  // dc. BeginDrawing ();
   dc. SetMapMode (wxMM_TEXT);
   dc. SetBrush (*(hbmp_brush [pattNr]));
   dc. SetPen (*wxTRANSPARENT_PEN);
   dc. SetTextBackground (TRANSLATE_COLOR (c_bgcol));
   dc. SetTextForeground (TRANSLATE_COLOR (colNr));

   dc. DrawRectangle (r -> lti, r -> ltj, r -> rbi - r -> lti,
      r -> rbj - r -> ltj);

   dc. SetBrush (wxNullBrush);
   dc. SetPen (wxNullPen);
 //  dc. EndDrawing ();
   return;
} /* FillRct */

void FillRct (Rct *r, int pattNr, int colNr)
// Draw a filled rectangle.
{
   if (!krakFrame)
      return;
   wxMutexGuiEnter ();

   wxClientDC dc (krakFrame);
   FillRct (dc, r, pattNr, colNr);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      FillRct (*(krakFrame -> dcMem), r, pattNr, colNr);
   memSection. Leave ();

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* FillRct */

inline double getAngle (int x, int y)
// Compute the angle of the point in the polar coordinates.
// Note that the screen coordinates go downwards.
{
   if (!x)
      return (y <= 0) ? 90 : 270;
   if (!y)
      return (x > 0) ? 0 : 180;
   double angle = atan (-y / (double) x) * 180 / 3.14159265;
   if (x < 0)
      return 180 + angle;
   if (angle < 0)
      return (360 + angle);
   return angle;
} /* getAngle */

inline void FillChord (wxDC &dc, int ltj, int lti, int rbj, int rbi,
   double start, double end, int pattNr, int colNr)
{
  // dc. BeginDrawing ();
   dc. SetMapMode (wxMM_TEXT);
   dc. SetBrush (*(hbmp_brush [pattNr]));
   dc. SetPen (*wxTRANSPARENT_PEN);
   dc. SetTextBackground (TRANSLATE_COLOR (c_bgcol));
   dc. SetTextForeground (TRANSLATE_COLOR (colNr));

   if (start == end)
      dc. DrawEllipse (ltj, lti, rbj - ltj, rbi - lti);
   else
      dc. DrawEllipticArc (ltj, lti, rbj - ltj, rbi - lti,
         start, end);

   dc. SetBrush (wxNullBrush);
   dc. SetPen (wxNullPen);
  // dc. EndDrawing ();
   return;
} /* FillChord */

void FillChord (int ltj, int lti, int rbj, int rbi, int bj, int bi,
   int ej, int ei, int pattNr, int colNr)
{
   if (!krakFrame)
      return;
   wxMutexGuiEnter ();

   double start, end;
   if ((bi == ei) && (bj == ej))
      start = end = 0;
   else
   {
      start = getAngle (bj - (rbj + ltj) / 2, bi - (rbi + lti) / 2);
      end = getAngle (ej - (rbj + ltj) / 2, ei - (rbi + lti) / 2);
      if (start > end)
         end += 360;
   }

   wxClientDC dc (krakFrame);
   FillChord (dc, ltj, lti, rbj, rbi, start, end, pattNr, colNr);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      FillChord (*(krakFrame -> dcMem), ltj, lti, rbj, rbi,
         start, end, pattNr, colNr);
   memSection. Leave ();

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* FillChord */

inline void Arc (wxDC &dc, wxPen &pen, int ltj, int lti, int rbj, int rbi,
   double start, double end)
{
  // dc. BeginDrawing ();
   dc. SetMapMode (wxMM_TEXT);
   dc. SetBrush (*wxTRANSPARENT_BRUSH);
   dc. SetPen (pen);

   if (start == end)
      dc. DrawEllipse (ltj, lti, rbj - ltj, rbi - lti);
   else
      dc. DrawEllipticArc (ltj, lti, rbj - ltj, rbi - lti,
         start, end);

   dc. SetBrush (wxNullBrush);
   dc. SetPen (wxNullPen);
  // dc. EndDrawing ();
   return;
} /* Arc */

void Arc (int ltj, int lti, int rbj, int rbi, int bj, int bi,
   int ej, int ei, int colNr)
{
   if (!krakFrame)
      return;

   double start, end;
   if ((bi == ei) && (bj == ej))
      start = end = 0;
   else
   {
      start = getAngle (bj - (rbj + ltj) / 2, bi - (rbi + lti) / 2);
      end = getAngle (ej - (rbj + ltj) / 2, ei - (rbi + lti) / 2);
      if (start > end)
         end += 360;
   }

   wxMutexGuiEnter ();

   wxPen pen (TRANSLATE_COLOR (colNr), 1, wxSOLID);

   wxClientDC dc (krakFrame);
   Arc (dc, pen, ltj, lti, rbj, rbi, start, end);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      Arc (*(krakFrame -> dcMem), pen, ltj, lti, rbj, rbi,
         start, end);
   memSection. Leave ();

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* Arc */

inline void FillRgn (wxDC &dc, int n, wxPoint points [],
   int pattNr, int colNr)
{
 //  dc. BeginDrawing ();
   dc. SetMapMode (wxMM_TEXT);
   dc. SetBrush (*(hbmp_brush [pattNr]));
   dc. SetPen (*wxTRANSPARENT_PEN);
   dc. SetTextBackground (TRANSLATE_COLOR (c_bgcol));
   dc. SetTextForeground (TRANSLATE_COLOR (colNr));

   dc. DrawPolygon (n, points);

   dc. SetBrush (wxNullBrush);
   dc. SetPen (wxNullPen);
  // dc. EndDrawing ();
   return;
} /* FillRgn */

void FillRgn (int *r, int lPoints, int pattNr, int colNr)
{
   if (!krakFrame || (lPoints <= 0))
      return;
   wxMutexGuiEnter ();

   // prepare the polygon points
   wxPoint *points = new wxPoint [lPoints];
   for (int i = 0; i < lPoints; i ++)
      points [i] = wxPoint (r [i + i], r [i + i + 1]);
   if (points [0] == points [lPoints - 1])
      lPoints --;

   wxClientDC dc (krakFrame);
   FillRgn (dc, lPoints, points, pattNr, colNr);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      FillRgn (*(krakFrame -> dcMem), lPoints, points,
         pattNr, colNr);
   memSection. Leave ();

   delete [] points;

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* FillRgn */

void SetBgCol (int col)
// Set background color.
{
   c_bgcol = col;
   return;
} /* SetBgCol */

void SetFgCol (int col)
// Set foreground color.
{
   c_fgcol = col;
   return;
} /* SetFgCol */

inline int DrawStrng (wxDC &dc, wxFont &font, const char *txt)
// Draw the given string and return its width.
{
   //dc. BeginDrawing ();

   // prepare for the text and the background rectangle drawing
   dc. SetMapMode (wxMM_TEXT);
   dc. SetFont (font);

   // draw the background rectangle first
   wxCoord width, height;
   dc. GetTextExtent (wxString (txt, wxConvUTF8), &width, &height);
   wxBrush brush (TRANSLATE_COLOR (c_bgcol), wxSOLID);
   dc. SetBrush (brush);
   dc. SetPen (*wxTRANSPARENT_PEN);
   dc. DrawRectangle (current_x, current_y, width, height);
   dc. SetBrush (wxNullBrush);

   // write the text on the background rectangle
   dc. SetMapMode (wxMM_TEXT);
   dc. SetTextForeground (TRANSLATE_COLOR (c_fgcol));
   dc. SetTextBackground (TRANSLATE_COLOR (c_bgcol));
   dc. DrawText (wxString (txt, wxConvUTF8), current_x, current_y);

  //dc. EndDrawing ();
   return width;
} /* DrawStrng */

void DrawStrng (const char *txt)
{
   if (!krakFrame)
      return;
   wxMutexGuiEnter ();

   wxFont font (fontSize, wxMODERN, wxNORMAL, wxNORMAL);

   wxClientDC dc (krakFrame);
   int width = DrawStrng (dc, font, txt);

   memSection. Enter ();
   if (krakFrame -> dcMem)
      DrawStrng (*(krakFrame -> dcMem), font, txt);
   memSection. Leave ();

   current_x += width;

   drawingFinished ();
   wxMutexGuiLeave ();
   yield ();
   return;
} /* DrawStrng */

void SetTextSize (int size)
// Set the font size in points.
{
   // remember the new font size
   fontSize = size;

   // measure the width of the letters in the font
   if (!krakFrame)
   {
      // make a reasonable guess if no window is open and quit
      fontWdth = size / 2;
      fontHght = size;
      return;
   }

   wxMutexGuiEnter ();
   wxClientDC dc (krakFrame);
   wxFont font (fontSize, wxMODERN, wxNORMAL, wxNORMAL);
   dc. SetMapMode (wxMM_TEXT);
   dc. SetFont (font);
   wxCoord width = 0, height = 0;
   dc. GetTextExtent (wxT("X"), &width, &height);
   fontWdth = width;
   fontHght = height;
   wxMutexGuiLeave ();

   return;
} /* SetTextSize */

int GetTextSize ()
{
   return fontSize;
} /* GetTextSize */

char *datetime ()
{
   wxDateTime x = wxDateTime::Now ();
   wxString str = x. Format ();

   static char *text = new char [100];
   strcpy (text, str. mb_str ());
   return text;
} /* datetime */

void OpenGraphics (int hrs, int vrs, int bgcol, int fgcol, int ltx, int lty)
{
   // do nothing if the graphics window is already open
   if (krakFrame || KrakThread::openGraphics)
      return;

   // initialize various data before opening the window
   set_colors ();
   SetBgCol (bgcol);
   SetFgCol (fgcol);
   set_pat ();

   // request the main thread to open the graphics window
   krakThread -> x = ltx;
   krakThread -> y = lty;
   krakThread -> width = hrs;
   krakThread -> height = vrs;
   krakThread -> bgColor = TRANSLATE_COLOR (bgcol);
   KrakThread::openGraphics = true;
   {
      wxMutexLocker lock (krakThread -> m_mutex);
      krakThread -> m_condition. Broadcast ();
   }

   // wait until the graphics window has been created
   krakThread -> m_done. Lock ();

   // adjust a nice font size - something not too small
   int textSize = 8;
   do
      SetTextSize (textSize);
   while ((textSize ++ < 14) && (fontHght < 14));

   yield ();
   return;
} /* OpenGraphics */

void CloseGraphics ()
{
   // do nothing if the graphics frame is not open
   if (!krakFrame)
      return;

   // close the frame and free allocated patterns
/* wxMutexGuiEnter ();
   krakFrame -> Destroy ();
   krakFrame = (KrakFrame *) NULL;
   wxMutexGuiLeave ();
   free_pat ();
*/
   yield ();
   return;
} /* CloseGraphics */

static long prevWatch = 0;
static int watchCycles = 0;
static const int tickSize = 32;
static const long cycleTicks = 0x07FFFFFFl;

long tickClock ()
// Return the number of clock ticks from program start.
{
   // read the stop-watch time
   long newWatch = stopWatch -> Time ();

   // if the stop-watch made a full cycle, remember this
   if (newWatch < prevWatch)
      watchCycles ++;

   // save the current stop-watch state for further use
   prevWatch = newWatch;

   // calculate the elapsed time in the given clock ticks
   long elapsedTime = ((unsigned long) newWatch) / tickSize;
   if (watchCycles)
      elapsedTime += watchCycles * cycleTicks;

   return elapsedTime;
} /* tickClock */

double Clock (void)
// Return the time from the program start in seconds as a double.
{
   return tickClock () * 0.032;
} /* Clock */

double tck2sec (long tck)
// Convert clock ticks to seconds.
{
   return tck * 0.0032;
} /* tck2sec */

long tckClock ()
// Return the number of clock ticks from program start.
{
   return tickClock ();
} /* tckClock */

/*
double RClock (void)
// ???
{
   gettimeofday(&tp,NULL);
   return ((double)tp.tv_sec);
}*/ /* RClock */


} /* namespace krak */
} /* namespace capd */


// last but not least, implement the wxWindows application
IMPLEMENT_APP (capd::krak::wxWin::KrakApp)

/// @}

