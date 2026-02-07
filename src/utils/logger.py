import logging


class Logger:
    """
    Only information, greater or equal to the level of logging.warning, can be output to the terminal.
    """

    def __init__(self, log_file):
        self.log_file = log_file

    def setup_logger(self, overwrite):
        """
        Set up the logger to write to a file. If overwrite=True, the log file will be overwritten,
        otherwise, logs will be appended to the file.

        Returns:
            logger: A logger instance specific to the given log file.
        """
        log_level = (
            logging.INFO
        )  # You can change this level to DEBUG, ERROR, etc. based on need

        # Create a logger instance specific to this file
        logger = logging.getLogger(self.log_file)

        # Set log level
        logger.setLevel(log_level)

        # Remove any existing handlers (to avoid duplicates in case the method is called multiple times)
        for handler in logger.handlers:
            logger.removeHandler(handler)

        if overwrite:
            # If overwrite is True, remove the file and create a new one
            file_handler = logging.FileHandler(
                self.log_file, mode="w"
            )  # 'w' mode to overwrite
        else:
            # If overwrite is False, append to the existing file
            file_handler = logging.FileHandler(
                self.log_file, mode="a"
            )  # 'a' mode to append

        # Set file handler format
        file_handler.setFormatter(
            logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
        )

        # Add file handler to the logger
        logger.addHandler(file_handler)

        # Create a console handler to output to the terminal
        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.CRITICAL + 1)
        console_handler.setFormatter(
            logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
        )

        # Add (silent) console handler
        logger.addHandler(console_handler)

        def terminal(msg):
            record = logging.LogRecord(
                name=logger.name,
                level=logging.INFO,
                pathname="<terminal>",
                lineno=0,
                msg=msg,
                args=(),
                exc_info=None,
            )
            file_handler.emit(record)
            console_handler.emit(record)

        logger.terminal = terminal

        return logger


class AttrDict(dict):
    def __getattr__(self, name):
        return self[name]


class DummyLogger:
    """
    A dummy logger that does nothing.
    """

    def __init__(self):
        pass

    def terminal(self, msg):
        pass

    def info(self, msg):
        pass

    def warning(self, msg):
        pass

    def error(self, msg):
        pass

    def debug(self, msg):
        pass
