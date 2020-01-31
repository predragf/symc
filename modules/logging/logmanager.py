import modules.logging.log as log
import logging


class LogManager:
    def __init__():
        pass

    @staticmethod
    def getLogger(loggerName=""):
        logger = log.setup_custom_logger(loggerName)
        logger = logging.getLogger('root')
        return logger
