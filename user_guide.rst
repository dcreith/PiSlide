==========
User Guide
==========

PiSlide is based on `David Hunt's <http://www.davidhunt.ie>` LapsePiTouch project.


PiSlide is an attempt at making a user friendly timelapse slide controller. Although
I enjoy building and programming these projects I also want them to be easy to use
and, most importantly, always work when I use them.

PiSlide will calculate the interval between images based on the slide motor
speed, the length of the slide, the shutter speed and a settling time.

Besides the TFT screen I also use a RGB LED to indicate the status of the
timelapse.

Primary Screen
--------------

.. image:: http://www.creith.net/wp-content/uploads/2015/03/primary.jpg
   :align: right

The primary screen provides info on the current session. The Start and Stop
buttons will launch or cancel the timelapse. The Gear button presents a
Parameter screen.

The current motor direction is shown on the primary screen and the parameter
screen immediately above either the Start or Stop button.

One the left side of the screen is the set shutter speed with the image count
immediately below. On the right side is the calculated pause time at the top
with the remaining time in the timelapse below.

At the center top of the screen a task indicator icon will be displayed while
the timelapse executes.

The screen backlight can be turned off from the primary screen by pressing
anywhere in the display area above the Start Stop buttons.


Parameters
----------

The Gear icon on the primary screen provides a parameter screen to update the
shutter duration, timelapse duration, number of images to take, the slide
length, the slide motor speed and the settling time before each image. Base on
these parameters, and an additional focus pause, the slide motor run time is
calculated and a pause time is determined.

.. image:: http://www.creith.net/wp-content/uploads/2015/03/parameters.jpg
   :align: right

Pressing the icon beside the parameter will present a keypad where and entry can
be made, press Update accept the parameter change. Some parameters accept
fractional seconds as entries. On this screen select either the 'S' for full
seconds or '1/S' for a fractional entry. The Clear button will clear the value
entirely, the Cancel button discards the change.

Motor direction can be set on the parameter screen. The slide
motor can be run from the parameter screen by pressing either the left or right
arrow.

Shutter Duration - the length of time to fire the shutter, should approximate the
camera's actual shutter speed but only controls the timing of triggering the shutter.
300 milliseconds will be added to the shutter duration for the focus trigger.

.. image:: http://www.creith.net/wp-content/uploads/2015/03/shutter.png
   :align: right

Timelapse Duration - the length of time expected to be shooting in minutes

.. image:: http://www.creith.net/wp-content/uploads/2015/03/duration.png
   :align: right

Images - the number of images to take

.. image:: http://www.creith.net/wp-content/uploads/2015/03/images.png
   :align: right

Settling Time - the length of pause to settle the slide before taking an image
 in seconds or fractions of seconds.

.. image:: http://www.creith.net/wp-content/uploads/2015/03/settle.png
   :align: right

Distance - the slide travel in millimeters

.. image:: http://www.creith.net/wp-content/uploads/2015/03/distance.png
   :align: right

Speed - the speed your slide travels in millimeters / second

.. image:: http://www.creith.net/wp-content/uploads/2015/03/speed.png
   :align: right


Keypads
-------

.. image:: http://www.creith.net/wp-content/uploads/2015/03/keypad.jpg
   :align: left

.. image:: http://www.creith.net/wp-content/uploads/2015/03/keypad_seconds.jpg
   :align: right
   
RGB LED
-------

White - application starting

Red - timelapse completed (stays on for 30 seconds following completion of
      timeplase)

Green - timelapse runnning

Blue - ready (standing by)

Yellow - unknown status
