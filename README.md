# XYModem
XYModem is a Java implementation of the XModem and YModem file
download protocols.  It supports:

* XModem-Checksum
* XModem-CRC
* XModem-1K
* YModem-Batch
* YModem-G

It also implements just enough of ZModem for AutoDownload support,
though that only works if the sending ZModem implemenation provides
automatic fallback to XModem or YModem.

## Usage

Create an implemenation of IOHandler, to provide I/O methods appropriate
for your environment.

Create a new instance of XYModem, giving it an instance of your IOHandler
implementation.

		XYModem xymodem = new XYModem(ioHandler);

After the sender has been instructed to begin an XModem or YModem download,
pass control to XYModem.

		xymodem.download();

XYModem will handle the handshaking and download process, using
`IOHandler.read(timeout)` to read bytes from the sender and
`IOHandler.write(ch)` to write bytes to the sender.

Each time a file download is complete, it will call
`IOHandler.received(download)` to pass details of the downloaded
file.  This may be called more than once for a batch download
(YModem-Batch or YModem-G).

When the download session is complete, `XYModem.download()` will return.

During the download process, `IOHandler.log(message)` and `IOHandler.progress(bytes, total)`
will be called with messages and download progress.

**AutoDownload**

Before a download has been initiated, incoming bytes can be checked for
a ZModem download signature.

		xymodem.autoDownloadDetect(ch);

This method will return `true` if a ZModem ZRQINIT header is detected,
indicating the sender is ready to begin download.  It can be used to
automatically initiate a download:

		if (xymodem.autoDownloadDetect(ch)) {
			xymodem.download();
		}

Please note:  If the sending ZModem implementation does not support
automatic fallback to XModem or YModem, the handshaking will time
out and `download()` will return, with the sender still waiting
for a ZModem download to begin.


## Dependencies
* [Java 8](https://www.oracle.com/java)
* [net.digger.util.crc.CRC](https://github.com/diggernet/JavaCRC)


## License
XYModem is provided under the terms of the GNU LGPLv3.
