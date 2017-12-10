/**
 * Copyright © 2017  David Walton
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package net.digger.protocol;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.FileTime;
import java.util.concurrent.TimeUnit;

/**
 * Encapsulates details of the downloaded file.
 * 
 * @author walton
 */
public class Download {
	/**
	 * Path to local copy of successfully downloaded file.
	 */
	public Path file;
	/**
	 * Name of downloaded file from sender, if available.
	 * Null if not sent.
	 */
	public String name = null;
	/**
	 * Length of downloaded file from sender, if available.
	 * Zero if not sent.
	 */
	public long length = 0;
	/**
	 * Modification time of downloaded file from sender, if available.
	 * Null if not sent.
	 */
	public FileTime modified = null;
	/**
	 * Mode of downloaded file from sender, if available.
	 * Zero if not sent.
	 */
	public int mode = 0;
	/**
	 * Serial number of downloaded file from sender, if available.
	 * Zero if not sent.
	 */
	public int serial = 0;

	/**
	 * Create a new Download, with no file name from sender.
	 * <p>
	 * Also creates the new local file for writing.
	 * 
	 * @throws AbortDownloadException If error creating local file.
	 */
	public Download() throws AbortDownloadException {
		this(null);
	}

	/**
	 * Create a new Download, with file name from sender.
	 * <p>
	 * Also creates the new local file for writing.
	 * 
	 * @param name Name of file to download
	 * @throws AbortDownloadException If error creating local file.
	 */
	public Download(String name) throws AbortDownloadException {
		try {
			// create a temp file
			file = Files.createTempFile("gecpdownload-", null);
			// if no file name was given, we are done
			if (name == null) {
				return;
			}
			// store the file name as given, before processing for use
			this.name = name;
			/*
			 * Chapter 5.  YMODEM Batch File Transmission
			 * If directories are included, they are delimited by /; i.e.,
			 * "subdir/foo" is acceptable, "subdir\foo" is not.
			 */
			// in case the given file name is a full path, use just the name portion of it
			int pos = name.lastIndexOf('/');
			Path filepath = Paths.get(name.substring(pos + 1)).getFileName();
			String filename = filepath.toString();
			// create a path using the temp file directory and the given file name
			Path newfile = file.resolveSibling(filename);
			// if the created path already exists, look for one which does not exist
			if (Files.exists(newfile)) {
				int i = 0;
				String fileext = null;
				pos = filename.lastIndexOf('.');
				// if filename has extension (ignoring . at start of name), break apart name and ext
				if (pos > 0) {
					fileext = filename.substring(pos + 1);
					filename = filename.substring(0, pos);
				}
				// append incrementing number to filename until a name is found which does not exist
				do {
					i++;
					if (fileext != null) {
						// if there is a file extension, use filename-#.ext
						newfile = file.resolveSibling(filename + '-' + i + '.' + fileext);
					} else {
						// if there is no file extension, use filename-#
						newfile = file.resolveSibling(filename + '-' + i);
					}
				} while (Files.exists(newfile));
			}
			// create a new file
			newfile = Files.createFile(newfile);
			// delete the original temp file
			Files.delete(file);
			file = newfile;
		} catch (InvalidPathException e) {
			// if can't create a named path, just fall back to using the temp file
			return;
		} catch (IOException e) {
			/*
			 * Chapter 5.  YMODEM Batch File Transmission
			 * If the file cannot be
			 * opened for writing, the receiver cancels the transfer with CAN characters
			 * as described above.
			 */
			throw new AbortDownloadException("Error creating file.", e);
		}
	}

	/**
	 * Store the modification time from the sender.
	 * 
	 * @param timestamp Modification timestamp
	 */
	public void setFileTime(long timestamp) {
		if (timestamp > 0) {
			modified = FileTime.from(timestamp, TimeUnit.SECONDS);
		}
	}

	/**
	 * Reset the downloaded file's modification time to the time given by
	 * the sender, if available.
	 */
	public void resetLastModified() {
		if (modified != null) {
			try {
				Files.setLastModifiedTime(file, modified);
			} catch (IOException e) {
				// just ignore the error
			}
		}
	}
}
