=======
Install
=======

This project is heavily based on David Hunt's LapsePiTouch and relies on the
Adafruit PiTFT project and the WiringPi libraries.

*See*

`David Hunt's Blog <http://www.davidhunt.ie/?p=3349>`

`LapsePiTouch at Github <https://github.com/climberhunt/LapsePiTouch>`

`Adafruit PiTFT setup instructions <http://learn.adafruit.com/adafruit-pitft-28-inch-resistive-touchscreen-display-raspberry-pi>`_.

`WiringPi-Python Setup instructions <https://github.com/WiringPi/WiringPi-Python>`_.

**Get the repo**::

    git clone https://github.com/dcreith/PiSlide.git

-------------------
Raspberry Pi Set Up
-------------------

I used the Raspbian Wheezy 20140918 image from
`Adafruit's PiTFT Easy Install Guide <https://learn.adafruit.com/adafruit-pitft-28-inch-resistive-touchscreen-display-raspberry-pi/easy-install>`
as the starting point for my install.

Image your SD card and on first boot (or with Raspi-config) set SSH on, Serial
Console off (I use the additional GPIO pines) and boot to command line.

When I installed in the PiTFT and python libraries in the suggested order I got
404's on the python installs. By installing the python-dev and python-setuptools
before the 'sudo apt-get update' everything installed cleanly.

Once the python environment is installed with the wiring Pi and wiring Pi 2
libraries get the PiSlide application from github.

1. wget https://github.com/dcreith/PiSlide/PiSlide.zip

2. Unzip & CD to PiSlide

3. sudo python pislide.py


**To run on boot**

Edit /etc/rc.local file::

    sudo nano /etc/rc.local

add the following before Exit 0

    cd /home/pi/pislide
    python pislide.py
