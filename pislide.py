# Pi-Slide timelapse controller for Raspberry Pi
# This must run as root (sudo python pislide.py) due to framebuffer, etc.
#
# http://www.adafruit.com/products/998  (Raspberry Pi Model B)
# http://www.adafruit.com/products/1601 (PiTFT Mini Kit)
#
# Prerequisite tutorials: aside from the basic Raspbian setup and PiTFT setup
# http://learn.adafruit.com/adafruit-pitft-28-inch-resistive-touchscreen-display-raspberry-pi
#
# pislide.py by Dave Creith (dave@creith.net)
# usability changes, use fractions of seconds, additional parameter entry
#
# based on lapse.py by David Hunt (dave@davidhunt.ie)
# based on cam.py by Phil Burgess / Paint Your Dragon for Adafruit Industries.
# BSD license, all text above must be included in any redistribution.

import wiringpi2
import atexit
import cPickle as pickle
import errno
import fnmatch
import io
import os
import pygame
import threading
import signal
import sys

from pygame.locals import *
from subprocess import call
from time import sleep

from datetime import datetime, timedelta

# UI classes ---------------------------------------------------------------

# Icon is a very simple bitmap class, just associates a name and a pygame
# image (PNG loaded from icons directory) for each.
# There isn't a globally-declared fixed list of Icons.  Instead, the list
# is populated at runtime from the contents of the 'icons' directory.

class Icon:

    def __init__(self, name):
      self.name = name
      try:
        self.bitmap = pygame.image.load(iconPath + '/' + name + '.png')
      except:
        pass

# Button is a simple tappable screen region.  Each has:
#  - bounding rect ((X,Y,W,H) in pixels)
#  - optional background color and/or Icon (or None), always centered
#  - optional foreground Icon, always centered
#  - optional single callback function
#  - optional single value passed to callback
# Occasionally Buttons are used as a convenience for positioning Icons
# but the taps are ignored.  Stacking order is important; when Buttons
# overlap, lowest/first Button in list takes precedence when processing
# input, and highest/last Button is drawn atop prior Button(s).  This is
# used, for example, to center an Icon by creating a passive Button the
# width of the full screen, but with other buttons left or right that
# may take input precedence (e.g. the Effect labels & buttons).
# After Icons are loaded at runtime, a pass is made through the global
# buttons[] list to assign the Icon objects (from names) to each Button.

class Button:

    def __init__(self, rect, **kwargs):
      self.rect     = rect # Bounds
      self.color    = None # Background fill color, if any
      self.iconBg   = None # Background Icon (atop color fill)
      self.iconFg   = None # Foreground Icon (atop background)
      self.bg       = None # Background Icon name
      self.fg       = None # Foreground Icon name
      self.callback = None # Callback function
      self.value    = None # Value passed to callback
      for key, value in kwargs.iteritems():
        if   key == 'color': self.color    = value
        elif key == 'bg'   : self.bg       = value
        elif key == 'fg'   : self.fg       = value
        elif key == 'cb'   : self.callback = value
        elif key == 'value': self.value    = value

    def selected(self, pos):
      x1 = self.rect[0]
      y1 = self.rect[1]
      x2 = x1 + self.rect[2] - 1
      y2 = y1 + self.rect[3] - 1
      if ((pos[0] >= x1) and (pos[0] <= x2) and
          (pos[1] >= y1) and (pos[1] <= y2)):
        if self.callback:
          if self.value is None: self.callback()
          else:                  self.callback(self.value)
        return True
      return False

    def draw(self, screen):
      if self.color:
        screen.fill(self.color, self.rect)
      if self.iconBg:
        screen.blit(self.iconBg.bitmap,
          (self.rect[0]+(self.rect[2]-self.iconBg.bitmap.get_width())/2,
           self.rect[1]+(self.rect[3]-self.iconBg.bitmap.get_height())/2))
      if self.iconFg:
        screen.blit(self.iconFg.bitmap,
          (self.rect[0]+(self.rect[2]-self.iconFg.bitmap.get_width())/2,
           self.rect[1]+(self.rect[3]-self.iconFg.bitmap.get_height())/2))

    def setBg(self, name):
      if name is None:
        self.iconBg = None
      else:
        for i in icons:
          if name == i.name:
            self.iconBg = i
            break

# UI callbacks -------------------------------------------------------------
# These are defined before globals because they're referenced by items in
# the global buttons[] list.

def motorCallback(n): # Pass 1 (next setting) or -1 (prev setting)
    global screenMode
    global motorRunning
    global motorDirection
    global motorpin
    global motorpinA
    global motorpinB
    # 1 is left
    # 2 is right
    # change motor direction
    # if motor is running then shut it off
    # if motor is not running then start it
    # motorDirection is extraeneous
    if n == 1:
        motorDirection = 1
        motorpin = motorpinA
        if motorRunning == 0:
            motorRunning = 1
            gpio.digitalWrite(motorpin,gpio.HIGH)
        else:
            motorRunning = 0
            gpio.digitalWrite(motorpinA,gpio.LOW)
            gpio.digitalWrite(motorpinB,gpio.LOW)
    elif n == 2:
        motorDirection = 0
        motorpin = motorpinB
        if motorRunning == 0:
            motorRunning = 1
            gpio.digitalWrite(motorpin,gpio.HIGH)
        else:
            motorRunning = 0
            gpio.digitalWrite(motorpinA,gpio.LOW)
            gpio.digitalWrite(motorpinB,gpio.LOW)
    elif n == 3:
        if motorRunning == 1:
            motorRunning = 0
            gpio.digitalWrite(motorpinA,gpio.LOW)
            gpio.digitalWrite(motorpinB,gpio.LOW)
        if motorDirection == 0:
            motorDirection = 1
            motorpin = motorpinA
        elif motorDirection == 1:
            motorDirection = 0
            motorpin = motorpinB

def numericCallback(n): # Pass 1 (next setting) or -1 (prev setting)
    global screenMode
    global returnScreen
    global numberstring
    global v
    global dict_idx

    if n < 10:
        numberstring = numberstring + str(n)
    elif n == 10:
        numberstring = numberstring[:-1*(len(numberstring))]
    elif n == 11:
        screenMode = 1
    elif n == 12:
        screenMode = returnScreen
        if numberstring:
            numeric = int(numberstring)
            v[dict_idx] = numeric
    elif n == 13:
        screenMode = returnScreen
        if len(numberstring) > 0:
            numeric = float(numberstring)
            v[dict_idx] = numeric
    elif n == 14:
        screenMode = returnScreen
        if len(numberstring) > 0:
            numeric = 1 / float(numberstring)
            v[dict_idx] = numeric

def settingCallback(n): # Pass 1 (next setting) or -1 (prev setting)
    global screenMode
    screenMode += n
    if screenMode < 1:               screenMode = len(buttons) - 1
    elif screenMode >= len(buttons): screenMode = 1

def valuesCallback(n): # Pass 1 (next setting) or -1 (prev setting)
    global screenMode
    global returnScreen
    global numberstring
    global numeric
    global v
    global dict_idx

    if n == -1:
        screenMode = 0
        saveSettings()
        reasonableValues()
        timelapseSettings()

    if n == 1:
        dict_idx='Shutter'
        # set the source icon here
        sValue = float(v[dict_idx])
        if (sValue < 1):
            numberstring = str(int(1 / sValue))
        else:
            numberstring = str(v[dict_idx])
        screenMode = 3
        returnScreen = 1
    elif n == 2:
        dict_idx='Timespan'
        numberstring = str(v[dict_idx])
        screenMode = 2
        returnScreen = 1
    elif n == 3:
        dict_idx='Images'
        numberstring = str(v[dict_idx])
        screenMode = 2
        returnScreen = 1
    elif n == 4:
        dict_idx='Distance'
        numberstring = str(v[dict_idx])
        screenMode = 2
        returnScreen = 1
    elif n == 5:
        dict_idx='Settle'
        sValue = float(v[dict_idx])
        if (sValue < 1):
            numberstring = str(int(1 / sValue))
        else:
            numberstring = str(v[dict_idx])
        screenMode = 3
        returnScreen = 1
    elif n == 6:
        dict_idx='Speed'
#		numberstring = str(v[dict_idx])
        numberstring = "30"
        screenMode = 2
        returnScreen = 1

def viewCallback(n): # Viewfinder buttons
    global screenMode, screenModePrior
    if n is 0:   # Gear icon
      screenMode = 1

def doneCallback(): # Exit settings
    global screenMode
    if screenMode > 0:
      saveSettings()
    screenMode = 0 # Switch back to main window

def startCallback(n): # start/Stop the timelapse thread
    global t, busy, threadExited
    global currentframe
    global consumed_time
    if n == 1:
        if busy == False:
            if (threadExited == True):
                # Re-instanciate the object for the next start
                t = threading.Thread(target=timeLapse)
                threadExited = False
            t.start()
    if n == 0:
        if busy == True:
            busy = False
            t.join()
            currentframe = 0
            consumed_time = 0
            task_indicator  = "done"
            # Re-instanciate the object for the next time around.
            t = threading.Thread(target=timeLapse)

def timeLapse():
    global busy, threadExited
    global v
    global motorpin
    global shutterpin
    global focuspin
    global settling_time
    global pause_time
    global shoot_time
    global travel_time
    global travel_pulse
    global frame_time
    global shutter_time
    global focus_pause
    global frame_interval
    global currentframe
    global consumed_time
    global task_indicator

    busy = True

#   timelapseSettings()

    for i in range( 1 , v['Images'] + 1 ):
        if busy == False:
            break

        # move slide forward on all but first image
        if i!=1:
            task_indicator = "travel"
            gpio.digitalWrite(motorpin,gpio.HIGH)
            pause_it(travel_pulse)
            gpio.digitalWrite(motorpin,gpio.LOW)

        task_indicator = "settling"
        pause_it(settling_time)

        # disable the backlight, critical for night timelapses, also saves power
#        os.system("echo '0' > /sys/class/gpio/gpio252/value")

        task_indicator = "fire"
        # trigger the focus
        gpio.digitalWrite(focuspin,gpio.HIGH)
        pause_it(focus_pause)

        # trigger the shutter
        gpio.digitalWrite(shutterpin,gpio.HIGH)
        pause_it(shutter_time)
        gpio.digitalWrite(shutterpin,gpio.LOW)
        gpio.digitalWrite(focuspin,gpio.LOW)

        currentframe = i

        #  enable the backlight
#        os.system("echo '1' > /sys/class/gpio/gpio252/value")

        task_indicator = "pause"
        pause_it(pause_time)

    currentframe = 0
    consumed_time = 0
    task_indicator  = "done"
    busy = False
    threadExited = True

def is_integer(s):
    try:
        int(s)
        return True
    except ValueError:
        return False

def is_float(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def reasonableValues():
    global v
    global dict_idx
    global focus_pause
    if not is_float(v['Settle']):    v['Settle'] = 0
    if not is_float(v['Shutter']):   v['Shutter'] = 1 / 60
    if not is_integer(v['Images']):  v['Images'] = 10
    if not is_integer(v['Speed']):   v['Speed'] = 30
    if not is_integer(v['Distance']):v['Distance'] = 500
    if not is_integer(v['Timespan']):v['Timespan'] = 30

    if    v['Shutter']==0: v['Shutter'] = 1 / 60
    elif  v['Shutter']<(1/8000): v['Shutter'] = 1 / 60
    elif  v['Shutter']>90: v['Shutter'] = 1 / 60

    if v['Images']==0 or v['Images'] > 500: v['Images'] = 10

    if v['Speed']==0: v['Speed'] = 30

    if    v['Distance']==0: v['Distance'] = 1000
    elif  v['Distance']<v['Speed']: v['Distance'] = v['Speed']
    elif  v['Distance']>5000: v['Distance'] = 1000

    if    v['Timespan']<(1): v['Timespan'] = 30
    elif  v['Timespan']>1440: v['Timespan'] = 60

def timelapseSettings():
    global v
    global dict_idx
    global settling_time
    global shutter_time
    global travel_pulse
    global pause_time
    global focus_pause
    global frame_interval
    global consumed_time
    global current_frame     #debug

    settling_time = float(v['Settle'])                              # time to wait before firing shutter
    shutter_time = float(v['Shutter'])                              # shutter speed
    frame_time = (shutter_time + settling_time + focus_pause) 		# time for 1 image in seconds
    shoot_time = frame_time * int(v['Images'])                      # time for all images in seconds
    travel_time = round((float(v['Distance']) / float(v['Speed'])),1)            # total travel time for full rail in seconds
    distance_between = round((float(v['Distance']) / (float(v['Images'])-1)),1)  # distance between shots in mm
    travel_pulse = round(distance_between / float(v['Speed']),1)    # travel time between images in seconds

    # set the pause time between shots to fill defined Timespan setting
    pause_time = (((int(v['Timespan']) * 60) - (shoot_time + travel_time)) / (int(v['Images'])-1))
    frame_interval = pause_time + frame_time                        # total time to take 1 image including pause
    consumed_time = 0

    #debug
    print "v['Shutter']....." + str(v['Shutter'])
    print "v['Timespan']...." + str(v['Timespan'])
    print "v['Images']......" + str(v['Images'])
    print "v['Distance']...." + str(v['Distance'])
    print "v['Settle']......" + str(v['Settle'])
    print "v['Speed']......." + str(v['Speed'])
    print "settling_time...." + str(settling_time)
    print "shutter_time....." + str(shutter_time)
    print "frame_time......." + str(frame_time)
    print "shoot_time......." + str(shoot_time)
    print "travel_time......" + str(travel_time)
    print "distance_between." + str(distance_between)
    print "travel_pulse....." + str(travel_pulse)
    print "pause_time......." + str(pause_time)
    print "frame_interval..." + str(frame_interval)
    print "currentframe....." + str(currentframe)
    remaining = round((float(v['Timespan']) * 60) - consumed_time,1)
    print "remaining........" + str(remaining)
    sec = timedelta(seconds=int(remaining))
    print "sec.............." + str(sec)
    #debug

def pause_it(n):
    global consumed_time

    consumed_time = consumed_time + n
    sleep(n)

def xPos(lbl,j,s,mf):
    labelwidth = mf.size(lbl)[0]
    l = [5,65,5,5]            # leftmost co-ordinates for screens 0->3
    r = [320,260,320,320]     # rightmost co-ordinates for screens 0->3
    if j==0:
        x = l[s]
    else:
        x = r[s] - (labelwidth + 5)
        if x < 0:
            x = 160
    return x

def targetIcon(p):
    rIcon = pi["done"]
    #debug
    print "targetIcon p..." + p
    if p:
        pl = str(p.lower())
        print "targetIcon pl..." + pl
        for i in icons:           #   For each icon...
            if pl == i.name:       #    Compare names; match?
                rIcon = i.bitmap    #     Use icon
    return rIcon

def signal_handler(signal, frame):
    print 'got SIGTERM'
    pygame.quit()
    sys.exit()

# Global stuff -------------------------------------------------------------

t = threading.Thread(target=timeLapse)
busy            = False
threadExited    = False
screenMode      =  0      # Current screen mode; default = viewfinder
screenModePrior = -1      # Prior screen mode (for detecting changes)
returnScreen    = 0
iconPath        = 'icons' # Subdirectory containing UI bitmaps (PNG format)

whitefont = (255, 255, 255)
smallfont = 24
mediumfont = 30
largefont = 50

numeric         = 0       # number from numeric keypad
numberstring	= "0"
motorRunning	= 0
motorDirection	= 0
focuspin        = 16       # focus pin to be updated
shutterpin      = 17
motorpinA       = 18
motorpinB       = 27
motorpin        = motorpinA
backlightpin    = 252

consumed_time   = 0.0
currentframe    = 0

# fall back defaults - to be removed
travel_pulse    = 0.0

framecount      = 100
settling_time   = 0.2
shutter_time    = 0.2
frame_interval  = 0.7
travel_time     = 2.0

# defined focus pause in milliseconds
focus_pause     = 0.3

task_indicator  = "done"
last_task       = task_indicator

dict_idx	    = "Shutter"
# shutter, settle are in seconds
# timespan is in minutes
# distance is in mm
# speed is mm/s
# images is a count
v = { "Shutter": 2,
    "Timespan": 60,
    "Images": 120,
    "Distance": 2000,
    "Speed": 30,
    "Settle": 1}

pi = {"settling": pygame.image.load(iconPath + '/settling.png'),
      "fire": pygame.image.load(iconPath + '/fire.png'),
      "travel": pygame.image.load(iconPath + '/travel.png'),
      "pause": pygame.image.load(iconPath + '/pause.png'),
      "done": pygame.image.load(iconPath + '/direction.png')}

md = {0: pygame.image.load(iconPath + '/directionleft.png'),
      1:pygame.image.load(iconPath + '/directionright.png')}

smd = {0: pygame.image.load(iconPath + '/littleleft.png'),
       1:pygame.image.load(iconPath + '/littleright.png')}
smdx = {0: 5,
        1: 285}

icons = [] # This list gets populated at startup

# buttons[] is a list of lists; each top-level list element corresponds
# to one screen mode (e.g. viewfinder, image playback, storage settings),
# and each element within those lists corresponds to one UI button.
# There's a little bit of repetition (e.g. prev/next buttons are
# declared for each settings screen, rather than a single reusable
# set); trying to reuse those few elements just made for an ugly
# tangle of code elsewhere.

buttons = [

  # Screen mode 0 is main view screen of current status
  [Button((  5,180,120, 60), bg='start', cb=startCallback, value=1),
   Button((130,180, 60, 60), bg='gear',   cb=viewCallback, value=0),
   Button((195,180,120, 60), bg='stop',  cb=startCallback, value=0)],

  # Screen 1 for changing values and setting motor direction
  [Button((0,    0, 60, 60), bg='shutter',  cb=valuesCallback, value=1),
   Button((0,   60, 60, 60), bg='timespan', cb=valuesCallback, value=2),
   Button((0,  120, 60, 60), bg='images',   cb=valuesCallback, value=3),
   Button((260,  0, 60, 60), bg='distance', cb=valuesCallback, value=4),
   Button((260, 60, 60, 60), bg='settle',   cb=valuesCallback, value=5),
   Button((260,120, 60, 60), bg='speed',    cb=valuesCallback, value=6),
   Button((0,  180, 60, 60), bg='left',     cb=motorCallback, value=1),
   Button((60 ,180, 60, 60), bg='direction',cb=motorCallback, value=3),
   Button((120,180, 60, 60), bg='right',    cb=motorCallback, value=2),
   Button((180,180,140, 60), bg='done',     cb=valuesCallback, value=-1)],

  # Screen 2 for numeric input
  [Button((  0,  0,320, 60), bg='box'),
   Button((180,120, 60, 60), bg='0',     cb=numericCallback, value=0),
   Button((  0,180, 60, 60), bg='1',     cb=numericCallback, value=1),
   Button((120,180, 60, 60), bg='3',     cb=numericCallback, value=3),
   Button(( 60,180, 60, 60), bg='2',     cb=numericCallback, value=2),
   Button((  0,120, 60, 60), bg='4',     cb=numericCallback, value=4),
   Button(( 60,120, 60, 60), bg='5',     cb=numericCallback, value=5),
   Button((120,120, 60, 60), bg='6',     cb=numericCallback, value=6),
   Button((  0, 60, 60, 60), bg='7',     cb=numericCallback, value=7),
   Button(( 60, 60, 60, 60), bg='8',     cb=numericCallback, value=8),
   Button((120, 60, 60, 60), bg='9',     cb=numericCallback, value=9),
   Button((240,120, 80, 60), bg='clear', cb=numericCallback, value=10),
   Button((180,180,140, 60), bg='update',cb=numericCallback, value=12),
   Button((180, 60,140, 60), bg='cancel',cb=numericCallback, value=11)],

  # Screen 3 for numeric input
  [Button((  0,  0,320, 60), bg='box'),
   Button((180,120, 60, 60), bg='0',       cb=numericCallback, value=0),
   Button((  0,180, 60, 60), bg='1',       cb=numericCallback, value=1),
   Button((120,180, 60, 60), bg='3',       cb=numericCallback, value=3),
   Button(( 60,180, 60, 60), bg='2',       cb=numericCallback, value=2),
   Button((  0,120, 60, 60), bg='4',       cb=numericCallback, value=4),
   Button(( 60,120, 60, 60), bg='5',       cb=numericCallback, value=5),
   Button((120,120, 60, 60), bg='6',       cb=numericCallback, value=6),
   Button((  0, 60, 60, 60), bg='7',       cb=numericCallback, value=7),
   Button(( 60, 60, 60, 60), bg='8',       cb=numericCallback, value=8),
   Button((120, 60, 60, 60), bg='9',       cb=numericCallback, value=9),
   Button((240,120, 80, 60), bg='clear',   cb=numericCallback, value=10),
   Button((180,180, 60, 60), bg='second',  cb=numericCallback, value=13),
   Button((240,180, 80, 60), bg='fraction',cb=numericCallback, value=14),
   Button((180, 60,140, 60), bg='cancel',  cb=numericCallback, value=11)]
]


# Assorted utility functions -----------------------------------------------


def saveSettings():
    global v
    try:
      outfile = open('pislide.pkl', 'wb')
      # Use a dictionary (rather than pickling 'raw' values) so
      # the number & order of things can change without breaking.
      pickle.dump(v, outfile)
      outfile.close()
    except:
      pass

def loadSettings():
    global v
    try:
      infile = open('pislide.pkl', 'rb')
      v = pickle.load(infile)
      infile.close()
    except:
      pass


# Initialization -----------------------------------------------------------

# Init framebuffer/touchscreen environment variables
os.putenv('SDL_VIDEODRIVER', 'fbcon')
os.putenv('SDL_FBDEV'      , '/dev/fb1')
os.putenv('SDL_MOUSEDRV'   , 'TSLIB')
os.putenv('SDL_MOUSEDEV'   , '/dev/input/touchscreen')


# Init pygame and screen
print "Initting..."
pygame.init()
print "Setting Mouse invisible..."
pygame.mouse.set_visible(False)
print "Setting fullscreen..."
modes = pygame.display.list_modes(16)
screen = pygame.display.set_mode(modes[0], FULLSCREEN, 16)

print "Loading Icons..."
# Load all icons at startup.
for file in os.listdir(iconPath):
  if fnmatch.fnmatch(file, '*.png'):
    icons.append(Icon(file.split('.')[0]))
# Assign Icons to Buttons, now that they're loaded
print"Assigning Buttons"
for s in buttons:        # For each screenful of buttons...
  for b in s:            #  For each button on screen...
    for i in icons:      #   For each icon...
      if b.bg == i.name: #    Compare names; match?
        b.iconBg = i     #     Assign Icon to Button
        b.bg     = None  #     Name no longer used; allow garbage collection
      if b.fg == i.name:
        b.iconFg = i
        b.fg     = None

# Set up GPIO pins
print "Init GPIO pins..."
gpio = wiringpi2.GPIO(wiringpi2.GPIO.WPI_MODE_GPIO)
gpio.pinMode(shutterpin,gpio.OUTPUT)
gpio.pinMode(focuspin,gpio.OUTPUT)
gpio.pinMode(motorpinA,gpio.OUTPUT)
gpio.pinMode(motorpinB,gpio.OUTPUT)
gpio.digitalWrite(motorpinA,gpio.LOW)
gpio.digitalWrite(motorpinB,gpio.LOW)
# I couldnt seem to get at pin 252 for the backlight using the usual method above,
# but this seems to work
os.system("echo 252 > /sys/class/gpio/export")
os.system("echo 'out' > /sys/class/gpio/gpio252/direction")
os.system("echo '1' > /sys/class/gpio/gpio252/value")

print"Load Settings"
loadSettings() # Must come last; fiddles with Button/Icon states
reasonableValues() # Validate that the execution parms make sense
timelapseSettings() # Calculate timelapse execution values

print "loading background.."
img    = pygame.image.load("icons/PiSlide.png")

# define the screen background from the image
#
if img is None or img.get_height() < 240: # Letterbox, clear background
  screen.fill(0)
if img:
  screen.blit(img,
    ((320 - img.get_width() ) / 2,
     (240 - img.get_height()) / 2))

# new stuff
#background = pygame.Surface(screen.get_size())
# new stuff

pygame.display.update()

sleep(1)

# Main loop ----------------------------------------------------------------

signal.signal(signal.SIGTERM, signal_handler)

print "mainloop.."
while True:

  # Process touchscreen input
  while True:

    for event in pygame.event.get():
      if(event.type is MOUSEBUTTONDOWN):
        pos = pygame.mouse.get_pos()
        for b in buttons[screenMode]:
          if b.selected(pos): break
      # why shut off the motor on mouse up ??????????
      elif(event.type is MOUSEBUTTONUP):
        motorRunning = 0
        gpio.digitalWrite(motorpinA,gpio.LOW)
        gpio.digitalWrite(motorpinB,gpio.LOW)

    # if not on screen 0 or changing screens then leave event loop
    if screenMode >= 0 or screenMode != screenModePrior: break


  if img is None or img.get_height() < 240: # Letterbox, clear background
    screen.fill(0)
  if img:
    screen.blit(img,
      ((320 - img.get_width() ) / 2,
       (240 - img.get_height()) / 2))

  # Overlay buttons on display and update
  for i,b in enumerate(buttons[screenMode]):
    b.draw(screen)

# keypad screens
  if screenMode == 3 or screenMode == 2:
    myfont = pygame.font.SysFont("Arial", largefont)
    myfont.set_bold(False)
    label = myfont.render(numberstring , 1, (whitefont))
    screen.blit(label, (xPos(numberstring,0,screenMode,myfont), 2))
    # blit the icon of the button pushed to get here
    screen.blit(targetIcon(dict_idx), (260, 0))

# parameter screen
  if screenMode == 1:
    myfont = pygame.font.SysFont("Arial", smallfont)
    myfont.set_bold(True)

    sValue = float(v['Shutter'])
    if (sValue < 1):
        numeric = int(1 / sValue)
        labeltext = "1/" + str(numeric) + "s"
    else:
        numeric = int(sValue)
        labeltext = str(numeric) + "s"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,0,screenMode,myfont), 10))

    labeltext = str(v['Timespan']) + "min"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,0,screenMode,myfont), 70))

    labeltext = str(v['Images'])
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,0,screenMode,myfont), 130))

    labeltext = str(v['Distance']) + "mm"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,1,screenMode,myfont), 10))

    sValue = float(v['Settle'])
    if (sValue == 0):
        numeric = int(sValue)
        label = myfont.render(str(numeric) + "s" , 1, (whitefont))
    elif (sValue < 1):
        numeric = int(1 / sValue)
        labeltext = "1/" + str(numeric) + "s"
    else:
        numeric = int(sValue)
        labeltext = str(numeric) + "s"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,1,screenMode,myfont), 70))

    labeltext = str(v['Speed']) + "mm/s"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,1,screenMode,myfont), 130))
#   current motor direction
    screen.blit(md[motorDirection], (60 ,180))

# initial (home) screen
  if screenMode == 0:
    myfont = pygame.font.SysFont("Arial", mediumfont)
    myfont.set_bold(False)

    if task_indicator != last_task:
        screen.blit(pi[task_indicator], (130, 2))

    sValue = float(v['Shutter'])
    if (sValue < 1):
        numeric = int(1 / sValue)
        labeltext = "1/" + str(numeric) + "s"
    else:
        numeric = int(sValue)
        labeltext = str(numeric) + "s"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,0,screenMode,myfont), 10))

#   run time
    labeltext = str(round(travel_pulse,0)) + "s"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,1,screenMode,myfont), 90))
#   pause time
    labeltext = str(round(pause_time,0)) + "s"
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,1,screenMode,myfont), 10))
#   images remaining
    labeltext = str(currentframe) + " of " + str(v['Images'])
    label = myfont.render(labeltext , 1, (whitefont))
    screen.blit(label, (xPos(labeltext,0,screenMode,myfont), 50))
#   time remaining
#    remaining = float((frame_interval * (v['Images'] - currentframe)))
    remaining = round((float(v['Timespan']) * 60) - consumed_time,1)
    if remaining > 0:
        sec = timedelta(seconds=int(remaining))
        d = datetime(1,1,1) + sec
        if d.hour > 0:
            labeltext = "%dh%dm%ds" % (d.hour, d.minute, d.second)
        else:
            labeltext = "%dm%ds" % (d.minute, d.second)
        label = myfont.render(labeltext , 1, (whitefont))
        screen.blit(label, (xPos(labeltext,1,screenMode,myfont), 50))
#   show the motor direction
    screen.blit(smd[motorDirection], (smdx[motorDirection],150))

  pygame.display.update()

  screenModePrior = screenMode
