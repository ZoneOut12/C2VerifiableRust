class TranslationError(ValueError):
    """Custom exception for translation errors."""

    def __init__(self, message):
        super().__init__(message)
